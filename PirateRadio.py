#!/usr/bin/env python3
# Local FM Tuner
# - tries several stream URLs per station and uses the first that answers
# - asks for browser location to detect where you are and load local stations
# - clicking '+ Log' automatically detects or assigns an FM frequency
# - '/api/autofill' looks up a stream URL by station name on Radio Browser

import os
import re
import sys
import copy
import json
import time
import shlex
import shutil
import socket
import signal
import tempfile
import threading
import pathlib
import subprocess
import webbrowser
import ssl
import http.client
import urllib.error
import urllib.request
from urllib.parse import urlencode, urlsplit, parse_qs
from functools import lru_cache
from concurrent.futures import ThreadPoolExecutor, as_completed, wait, FIRST_COMPLETED
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler

# Force curl to skip certificate checks for every station. Normally leave False:
# the script retries without verification automatically if the check fails.
INSECURE_SSL = False

# Optional: force an mpg123 output module (e.g. "pulse" or "alsa").
MPG123_OUTPUT = None

# Stations: frequency -> (name, [candidate stream URLs, tried in order]).
STATIONS = {
    "97.5": ("Heart Essex", [
        "https://media-ssl.musicradio.com/HeartEssex",
        "https://icecast.thisisdax.com/HeartEssexMP3",
        "https://ice-sov.musicradio.com/HeartEssexMP3",
    ]),
    "105.1": ("Radio Essex", [
        "https://icecast.as34763.net/radioessex",
    ]),
    "103.7": ("Funky SX", [
        # Current Funky SX / Digital City Radio endpoint (HTTP, AAC+).
        # mpg123 cannot decode AAC — the player chain falls through to
        # ffplay / mpv, which can.
        "http://stream1.funkyessex.co.uk:8000/mp3128",
        # Older host kept as fallback in case the primary goes down.
        "https://stream.funkysx.com/funkysx.mp3",
    ]),
}

# curl exit codes that mean "TLS/certificate problem"
SSL_ERRORS = {35, 51, 58, 59, 60, 77, 82, 83, 90, 91}

_good_url = {}       # station name -> (url, insecure, content_type) that worked last time
_good_method = None  # playback method that worked last time (tried first)
_bad_until = {}      # station name -> time before which we skip re-probing


_PLAYLIST_TYPES = {"audio/x-mpegurl", "audio/mpegurl", "application/x-mpegurl",
                   "audio/x-scpls", "application/pls", "application/x-scpls"}


def _playlist_url(text):
    """First stream URL inside an .m3u/.pls playlist (None for HLS or junk)."""
    if "#EXT-X-" in text:
        return None
    for line in text.splitlines():
        line = line.strip()
        if line.lower().startswith("file") and "=" in line:
            line = line.split("=", 1)[1].strip()
        if line.lower().startswith(("http://", "https://")):
            return line
    return None


def probe(url, insecure, depth=0):
    """Open the stream and look at what really comes back. Returns
    (curl-style exit, http_code, content_type, error, final_url). Web pages and
    playlists are NOT audio: playlists are followed, anything else is rejected."""
    ctx = ssl.create_default_context()
    if insecure:
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})

    def fail(rc, msg):
        return rc, "", "", msg, url
    try:
        with urllib.request.urlopen(req, timeout=5, context=ctx) as r:
            head = r.read(2048)
            ctype = r.headers.get("Content-Type", "")
            kind = ctype.split(";")[0].strip().lower()
            lead = head.lstrip()
            if (kind.startswith("text/") or kind in _PLAYLIST_TYPES or lead[:1] == b"<"
                    or lead.startswith((b"#EXTM3U", b"[playlist", b"[Playlist"))):
                inner = _playlist_url((head + r.read(16384)).decode("utf-8", "replace"))
                if inner and depth < 2 and inner != url:
                    return probe(inner, insecure, depth + 1)
                return fail(1, f"Not an audio stream (server sent {kind or 'text'})")
            return 0, str(r.status), ctype, "", r.geturl()
    except urllib.error.HTTPError as e:
        return 22, str(e.code), "", f"HTTP {e.code}", url
    except urllib.error.URLError as e:
        why = e.reason
        if isinstance(why, ssl.SSLError):
            return fail(60, str(why))
        if isinstance(why, socket.gaierror):
            return fail(6, f"Could not resolve host: {urlsplit(url).hostname}")
        if isinstance(why, (socket.timeout, TimeoutError)):
            return fail(28, "Connection timed out")
        return fail(7, str(why))
    except ssl.SSLError as e:
        return fail(60, str(e))
    except (socket.timeout, TimeoutError):
        return fail(28, "Connection timed out")
    except http.client.BadStatusLine as e:      # old Shoutcast servers answer "ICY 200 OK"
        if "ICY" in str(e):
            return 0, "200", "audio/mpeg", "", url
        return fail(1, str(e))
    except Exception as e:
        return fail(1, str(e))


def _check(url):
    insecure = INSECURE_SSL
    rc, code, ctype, err, final = probe(url, insecure)
    if rc in SSL_ERRORS and not insecure:
        insecure = True
        rc, code, ctype, err, final = probe(url, True)
    return final, insecure, code, ctype, err or f"HTTP {code or 'none'}"


def resolve_stream(urls):
    """Probe all candidate URLs in parallel and return the best working one.
    List order is priority: a faster lower-ranked URL only wins if every
    higher-ranked one has failed, or is still silent after 1.5s."""
    ex = ThreadPoolExecutor(max_workers=len(urls))
    futs = {ex.submit(_check, u): i for i, u in enumerate(urls)}
    pending, results, deadline = set(futs), {}, None
    try:
        while pending:
            timeout = None if deadline is None else max(0, deadline - time.time())
            done, pending = wait(pending, timeout=timeout, return_when=FIRST_COMPLETED)
            for fut in done:
                i = futs[fut]
                url, insecure, code, ctype, err = fut.result()
                if code == "200":
                    results[i] = (url, insecure, ctype)
                else:
                    results[i] = None
                    print(f"    [x] {urls[i]}\n        {err}")
            ok = sorted(k for k, v in results.items() if v)
            if ok and (not done or all(j in results for j in range(ok[0]))):
                return results[ok[0]]
            if ok and deadline is None:
                deadline = time.time() + 1.5
        ok = sorted(k for k, v in results.items() if v)
        return results[ok[0]] if ok else None
    finally:
        ex.shutdown(wait=False, cancel_futures=True)


@lru_cache(maxsize=None)
def detect_mpg123_output():
    """Ask mpg123 which audio output modules are listed (may still fail to load)."""
    try:
        res = subprocess.run(["mpg123", "--list-modules"],
                             capture_output=True, text=True, timeout=5)
    except Exception:
        return None
    available = set()
    for line in (res.stdout + res.stderr).splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[1] == "output":
            available.add(parts[0])
    for name in ("pulse", "alsa", "jack", "sdl", "portaudio", "openal"):
        if name in available:
            return name
    return None


@lru_cache(maxsize=None)
def flatpak_mpv_installed():
    if not shutil.which("flatpak"):
        return False
    try:
        r = subprocess.run(["flatpak", "info", "io.mpv.Mpv"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=5)
    except Exception:
        return False
    return r.returncode == 0


def build_candidates(url, insecure=False, ctype=""):
    """Return a list of (name, shell command) playback methods to try in order.
    curl fetches the stream (so -k applies to every player) and pipes it in."""
    have = shutil.which
    if not have("curl"):
        return []
    # shlex.quote protects against shell metacharacters in URLs (no shell injection).
    quoted_url = shlex.quote(url)
    src = f'curl -sSLfN{"k" if insecure else ""} {quoted_url}'
    c = []

    if have("mpg123"):
        module = MPG123_OUTPUT or detect_mpg123_output()
        if module:
            c.append((f"mpg123 ({module})", f"{src} | mpg123 -q -o {module} -"))
        # The stdout pipe does not need an mpg123 output module, so try it
        # whenever mpg123 exists (independent of module detection).
        if have("pw-play"):
            c.append(("mpg123 -> pw-play",
                      f"{src} | mpg123 -q -s -r 44100 --stereo - | "
                      f"pw-play --rate 44100 --channels 2 --format s16 -"))
    if have("mpv"):
        c.append(("mpv", f"{src} | mpv --no-video --really-quiet -"))
    if have("ffplay"):
        c.append(("ffplay", f"{src} | ffplay -nodisp -autoexit -loglevel error -i -"))
    if flatpak_mpv_installed():
        c.append(("mpv (flatpak)",
                  f"{src} | flatpak run io.mpv.Mpv --no-video --really-quiet -"))
    if have("gst-play-1.0") and not insecure:
        c.append(("GStreamer", f'gst-play-1.0 --no-interactive {quoted_url}'))
    not_mp3 = any(x in (ctype or "").lower() for x in ("aac", "ogg", "mp4", "flac", "opus"))
    # mpg123 only decodes MP3: for other formats try it last (it just makes noise/silence)
    c.sort(key=lambda m: (not_mp3 and m[0].startswith("mpg123"), m[0] != _good_method))
    return c


def stop_playback(proc):
    """Kill the whole pipeline (curl + player), not just the shell."""
    if proc and proc.poll() is None:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        except Exception:
            try:
                proc.terminate()
            except Exception:
                pass
        try:
            proc.wait(timeout=1)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass


def try_play(candidates, start=0, still_current=None):
    """Try each method (beginning at `start`) until one stays running.
    `still_current` is a zero-arg callable; if it returns False, we abort
    immediately without marking anything as failed."""
    global _good_method
    n = len(candidates)
    for k in range(n):
        if still_current is not None and not still_current():
            return None, -1, None
        i = (start + k) % n
        name, cmd = candidates[i]
        log = tempfile.TemporaryFile(mode="w+")
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.DEVNULL,
                                stderr=log, start_new_session=True)
        deadline = time.time() + 1.0
        while proc.poll() is None and time.time() < deadline:
            if still_current is not None and not still_current():
                stop_playback(proc)
                log.close()
                return None, -1, None
            time.sleep(0.05)
        if proc.poll() is None:
            _good_method = name
            log.close()
            return proc, i, name
        log.seek(0)
        lines = [l for l in log.read().strip().splitlines() if l.strip()]
        log.close()
        print(f"    [x] {name} failed" + (": " + " | ".join(lines[-2:]) if lines else ""))
    return None, -1, None


# ---------------------------------------------------------------------------
# Web UI: run this script, a browser tab opens with the radio.
# ---------------------------------------------------------------------------
PORT = 8765
LOGFILE = pathlib.Path(__file__).resolve().parent / "logbook.json"

DEFAULT_LOG = [{"freq": 95.3, "name": "BBC Essex", "urls": [],
                "note": "Southend relay - add a stream URL to hear it"}] + \
              [{"freq": float(f), "name": n, "urls": list(u), "note": ""}
               for f, (n, u) in STATIONS.items()]

DEFAULT_TAGS = {"Heart Essex": ["pop", "hits", "adult contemporary"],
                "Radio Essex": ["pop", "hits", "local"],
                "Funky SX": ["dance", "urban"],
                "BBC Essex": ["talk", "news", "local"]}


def get_volume():
    """System output volume 0-100 (PipeWire/PulseAudio), or None if unavailable."""
    try:
        if shutil.which("wpctl"):
            out = subprocess.run(["wpctl", "get-volume", "@DEFAULT_AUDIO_SINK@"],
                                 capture_output=True, text=True, timeout=3).stdout
            return round(float(out.split()[1]) * 100)
        if shutil.which("pactl"):
            out = subprocess.run(["pactl", "get-sink-volume", "@DEFAULT_SINK@"],
                                 capture_output=True, text=True, timeout=3).stdout
            return int(re.search(r"(\d+)%", out).group(1))
    except Exception:
        pass
    return None


def set_volume(level):
    level = max(0, min(100, int(level)))
    try:
        if shutil.which("wpctl"):
            subprocess.run(["wpctl", "set-volume", "@DEFAULT_AUDIO_SINK@", f"{level / 100:.2f}"],
                           timeout=3)
        elif shutil.which("pactl"):
            subprocess.run(["pactl", "set-sink-volume", "@DEFAULT_SINK@", f"{level}%"], timeout=3)
    except Exception:
        pass
    return level


class Radio:
    def __init__(self):
        self.lock = threading.Lock()
        self.gen = 0
        self.proc = None
        self.freq = 97.5
        self.status, self.msg, self.station = "off", "Radio off", ""
        self.browser_url = ""
        self.play_entry, self.play_start = None, None
        self.volume, self._vol_t = get_volume(), time.time()
        try:
            self.log = json.loads(LOGFILE.read_text())
        except Exception:
            self.log = copy.deepcopy(DEFAULT_LOG)
        for e in self.log:
            e.setdefault("urls", [])
            dflt = next((u for n, u in STATIONS.values() if n == e["name"]), None)
            if dflt:   # built-in stations always try their current addresses first
                e["urls"] = list(dflt) + [x for x in e["urls"] if x not in dflt]
            e.setdefault("note", "")
            e.setdefault("heard", 0)
            e.setdefault("last", "")
            e.setdefault("fav", False)
            e.setdefault("secs", 0)
            e.setdefault("tags", DEFAULT_TAGS.get(e["name"], []))
        self._dirty = False
        threading.Thread(target=self._save_loop, daemon=True).start()

    def save(self):
        """Mark the logbook dirty; a background thread flushes it shortly after."""
        self._dirty = True

    def _write_log(self):
        try:
            LOGFILE.write_text(json.dumps(self.log, indent=2))
        except OSError as e:
            print("[!] Could not save logbook:", e)

    def _save_loop(self):
        while True:
            time.sleep(1.2)
            if self._dirty:
                self._dirty = False
                self._write_log()

    def flush(self):
        if getattr(self, "_dirty", False):
            self._dirty = False
            self._write_log()

    def _bank(self):
        """Add the current listening session to that station's total (lock held)."""
        if self.play_entry is not None and self.play_start:
            self.play_entry["secs"] += time.time() - self.play_start
            self.save()
        self.play_entry, self.play_start = None, None

    def _log_view(self):
        live = time.time() - self.play_start if self.play_start else 0
        return [dict(e, secs=e["secs"] + (live if e is self.play_entry else 0)) for e in self.log]

    def snapshot(self):
        with self.lock:
            return self._log_view()

    def set_vol(self, level):
        v = set_volume(level)
        with self.lock:
            self.volume, self._vol_t = v, time.time()

    def _auto_freq(self, name="", tags=""):
        """Extract FM frequency from name/tags or pick an open dial frequency."""
        text = f"{name} {tags}"
        m = re.search(r"\b(8[7-9]|9\d|10[0-8])\.\d\b", text)
        if m:
            g = round(float(m.group(0)), 1)
            if 87.5 <= g <= 108.0 and not any(abs(e["freq"] - g) < 0.05 for e in self.log):
                return g, False
        h = 0
        for ch in str(name):
            h = ((h * 31) + ord(ch)) & 0xFFFFFFFF
        for gap in (0.15, 0.05):
            for k in range(206):
                c = round(87.5 + ((h + k) % 206) / 10.0, 1)
                if not any(abs(e["freq"] - c) < gap for e in self.log):
                    return c, True
        return 87.5, True

    def state(self):
        if time.time() - self._vol_t > 4:
            v = get_volume()
            self._vol_t = time.time()
            if v is not None:
                self.volume = v
        with self.lock:
            if self.status == "playing" and self.proc and self.proc.poll() is not None:
                self._bank()
                _good_url.pop(self.station, None)
                self.proc = None
                self.browser_url = ""
                self.status, self.msg = "error", "Stream ended - tune again"
            return {
                "freq": self.freq,
                "status": self.status,
                "msg": self.msg,
                "station": self.station,
                "browser_url": self.browser_url,
                "volume": self.volume,
                "log": self._log_view(),
            }

    def _set(self, g, status, msg, station="", browser_url=""):
        with self.lock:
            if g == self.gen:
                self.status, self.msg, self.station = status, msg, station
                self.browser_url = browser_url

    def tune(self, f):
        with self.lock:
            if self.status in ("playing", "tuning") and abs(self.freq - f) < 0.05:
                return
            self.gen += 1
            g = self.gen
            self._bank()
            old = self.proc
            self.proc = None
            self.browser_url = ""
            self.freq = f
            self.status, self.msg, self.station = "tuning", "Tuning...", ""
        threading.Thread(target=self._worker, args=(f, g, old), daemon=True).start()

    def _ensure_logged(self, entry):
        """First successful play of a dial station adds it to the logbook (lock held)."""
        if not any(x is entry for x in self.log):
            self.log.append(entry)

    def hush(self):
        """Silence the local player while the dial is being scanned (the browser
        previews take over until the knob settles)."""
        with self.lock:
            if self.status != "playing":
                return
            self.gen += 1
            self._bank()
            old = self.proc
            self.proc = None
            self.browser_url = ""
            self.status, self.msg, self.station = "static", "Scanning…", ""
        stop_playback(old)

    def stop(self):
        with self.lock:
            self.gen += 1
            self._bank()
            stop_playback(self.proc)
            self.proc = None
            self.browser_url = ""
            self.status, self.msg, self.station = "off", "Radio off", ""

    def _worker(self, f, g, old=None):
        stop_playback(old)
        with self.lock:
            entry = next((e for e in self.log if abs(e["freq"] - f) <= 0.05), None)
            if not entry:
                d = next((x for x in self.dial if abs(x["freq"] - f) <= 0.05), None)
                if d:   # a dial station you haven't logged yet: logged once it plays
                    entry = {"freq": d["freq"], "name": d["name"], "urls": [d["url"]],
                             "note": ", ".join(x for x in (d.get("state"), d.get("country")) if x),
                             "heard": 0, "last": "", "fav": False, "secs": 0,
                             "tags": [t.strip().lower() for t in (d.get("tags") or "").split(",")
                                      if t.strip()][:6]}
            found = (entry["name"], list(entry["urls"])) if entry else None
        if not entry:
            return self._set(g, "static", "Static - nothing logged on this frequency")
        name, urls = found
        if not urls:
            return self._set(g, "static", f"{name} is on air, but no stream is set", name)
        self._play_urls(g, name, urls, entry)

    def play_url(self, name, url):
        """Play any stream (used by the directory) without touching the dial."""
        with self.lock:
            self.gen += 1
            g = self.gen
            self._bank()
            old = self.proc
            self.proc = None
            self.browser_url = ""
            self.status, self.msg, self.station = "tuning", "Connecting...", name
        threading.Thread(target=self._play_urls, args=(g, name, [url], None, old),
                         daemon=True).start()

    def _play_urls(self, g, name, urls, entry, old=None):
        proc = method = None
        reached_url = None
        if time.time() < _bad_until.get(name, 0):
            return self._set(g, "error", f"{name} — stream unavailable, retrying shortly", name)
        cached = _good_url.get(name)
        for res in ([cached] if cached else []) + [None]:
            if res is None:
                res = resolve_stream(urls)
                if not res or g != self.gen:
                    break
            url, insecure, ctype = res
            reached_url = url
            proc, _, method = try_play(build_candidates(url, insecure, ctype),
                                       still_current=lambda: g == self.gen)
            if not proc and not insecure and g == self.gen:
                insecure = True
                proc, _, method = try_play(build_candidates(url, True, ctype),
                                           still_current=lambda: g == self.gen)
            if proc:
                _good_url[name] = (url, insecure, ctype)
                break
            _good_url.pop(name, None)

        if not proc and g == self.gen:
            # If stream is reachable but no local CLI player worked, play in the browser
            if reached_url:
                with self.lock:
                    if g != self.gen:
                        return
                    self.proc = None
                    self.browser_url = reached_url
                    self.play_entry, self.play_start = entry, time.time()
                    self.status, self.msg, self.station = "playing", "via Browser Audio", name
                    if entry:
                        self._ensure_logged(entry)
                        entry["heard"] += 1
                        entry["last"] = time.strftime("%d %b %H:%M")
                        self.save()
                return
            _bad_until[name] = time.time() + 12
            return self._set(g, "error", f"Can't reach a stream for {name}", name)

        with self.lock:
            if g != self.gen:
                stop_playback(proc)
                return
            if not proc:
                self.status, self.msg = "error", "No audio player worked (see terminal)"
                return
            self.proc = proc
            self.browser_url = ""
            self.play_entry, self.play_start = entry, time.time()
            self.status, self.msg, self.station = "playing", f"via {method}", name
            if entry:
                self._ensure_logged(entry)
                entry["heard"] += 1
                entry["last"] = time.strftime("%d %b %H:%M")
                self.save()

    def edit(self, b):
        with self.lock:
            op = b.get("op")
            raw_freq = b.get("freq")
            if op == "add" and b.get("name"):
                name = str(b["name"])[:60]
                url = str(b.get("url", "")).strip()
                tags_str = str(b.get("tags", ""))
                note = str(b.get("note", ""))[:200]
                auto = False
                try:
                    f = round(float(raw_freq), 1)
                    if not (87.5 <= f <= 108.0):
                        f = None
                except (ValueError, TypeError):
                    f = None
                if f is None:
                    have = next((e for e in self.log if url and url in e["urls"]), None)
                    if have:
                        f = have["freq"]
                    else:
                        f, auto = self._auto_freq(name, tags_str)
                if auto and "Auto-assigned" not in note:
                    note = ("Auto-assigned dial spot · " + note) if note else "Auto-assigned dial spot"
                old = next((e for e in self.log if abs(e["freq"] - f) < 0.05), None)
                new = {
                    "freq": f,
                    "name": name,
                    "note": note[:200],
                    "urls": [url] if url else (old["urls"] if old else []),
                    "heard": old["heard"] if old else 0,
                    "last": old["last"] if old else "",
                    "secs": old["secs"] if old else 0,
                    "fav": old["fav"] if old else False,
                    "tags": [t.strip().lower() for t in tags_str.split(",") if t.strip()][:6]
                    or (old["tags"] if old else []),
                }
                if old is not None and old is self.play_entry:
                    self.play_entry = new
                self.log = [e for e in self.log if abs(e["freq"] - f) >= 0.05] + [new]
                self.save()
                return f

            try:
                f = round(float(raw_freq or 0), 1)
            except (ValueError, TypeError):
                f = 0.0
            if op == "fav":
                for e in self.log:
                    if abs(e["freq"] - f) < 0.05:
                        e["fav"] = not e["fav"]
            elif op == "del":
                if self.play_entry is not None and abs(self.play_entry["freq"] - f) < 0.05:
                    self.play_entry, self.play_start = None, None
                self.log = [e for e in self.log if abs(e["freq"] - f) >= 0.05]
            elif op == "note":
                for e in self.log:
                    if abs(e["freq"] - f) < 0.05:
                        e["note"] = str(b.get("note", ""))[:200]
            self.save()
            return f


radio = Radio()
radio.dial = []     # region stations spread across the FM dial (not yet in the logbook)
_rb_cache = {}
_rec_cache = {}

RB_MIRRORS = (
    "https://all.api.radio-browser.info/json/",
    "https://de1.api.radio-browser.info/json/",
    "https://fi1.api.radio-browser.info/json/",
)


def _http_json(url, timeout=12):
    """Fetch JSON from a URL using curl (with -k retry) or urllib fallback."""
    if shutil.which("curl"):
        for flags in ("-sSL", "-sSLk"):
            r = subprocess.run(
                ["curl", flags, "-A", "Mozilla/5.0", "--max-time", str(timeout), url],
                capture_output=True, text=True
            )
            if r.returncode == 0 and r.stdout.strip():
                try:
                    return json.loads(r.stdout)
                except ValueError:
                    pass
    for insecure in (False, True):
        ctx = ssl.create_default_context()
        if insecure:
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        try:
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
                return json.loads(resp.read().decode("utf-8", errors="replace"))
        except Exception:
            continue
    raise RuntimeError(f"Could not reach {url}")


def rb(path, params=None):
    """Query the Radio Browser community directory across mirrors."""
    key = path + json.dumps(params or {}, sort_keys=True)
    if key in _rb_cache:
        return _rb_cache[key]
    qs = ("?" + urlencode(params)) if params else ""
    last_err = None
    for base in RB_MIRRORS:
        try:
            data = _http_json(base + path + qs, timeout=12)
            if isinstance(data, list):
                if path in ("countries", "states"):
                    _rb_cache[key] = data
                return data
        except Exception as e:
            last_err = e
    if last_err:
        raise last_err
    return []


def geolocate_api(q):
    """Reverse-geocode lat/lon (or IP fallback) into city, state/county, and country."""
    lat = (q.get("lat") or "").strip()
    lon = (q.get("lon") or "").strip()
    if lat and lon:
        # Try BigDataCloud first (fast, no rate limit, returns county/state/city cleanly)
        try:
            bdc_url = "https://api.bigdatacloud.net/data/reverse-geocode-client?" + urlencode({
                "latitude": lat, "longitude": lon, "localityLanguage": "en"
            })
            d = _http_json(bdc_url, timeout=8)
            city = d.get("city") or d.get("locality") or ""
            state = d.get("principalSubdivision") or ""
            # Check administrative levels for county (e.g. "Essex")
            for adm in (d.get("localityInfo") or {}).get("administrative") or []:
                name = adm.get("name", "")
                if adm.get("adminLevel") in (6, 5) and name and "United Kingdom" not in name:
                    state = name
                    break
            return {
                "city": city,
                "state": state,
                "country": d.get("countryName", ""),
                "countrycode": (d.get("countryCode") or "").upper(),
                "lat": float(lat),
                "lon": float(lon),
            }
        except Exception:
            pass
        # Fallback to OpenStreetMap Nominatim
        try:
            nom_url = "https://nominatim.openstreetmap.org/reverse?" + urlencode({
                "format": "jsonv2", "lat": lat, "lon": lon, "zoom": 10
            })
            d = _http_json(nom_url, timeout=8)
            addr = d.get("address", {})
            city = addr.get("city") or addr.get("town") or addr.get("village") or addr.get("municipality") or ""
            state = addr.get("county") or addr.get("state_district") or addr.get("state") or ""
            return {
                "city": city,
                "state": state,
                "country": addr.get("country", ""),
                "countrycode": (addr.get("country_code") or "").upper(),
                "lat": float(lat),
                "lon": float(lon),
            }
        except Exception:
            pass

    # Fallback: IP geolocation if browser GPS fails
    try:
        d = _http_json("https://ipapi.co/json/", timeout=8)
        return {
            "city": d.get("city", ""),
            "state": d.get("region", ""),
            "country": d.get("country_name", ""),
            "countrycode": (d.get("country_code") or "").upper(),
            "lat": d.get("latitude"),
            "lon": d.get("longitude"),
        }
    except Exception:
        return {"city": "", "state": "", "country": "", "countrycode": "GB"}


def autofill_stream(q):
    """Look up a station name on Radio Browser and return candidate stream URLs."""
    name = (q.get("name") or "").strip()
    country = (q.get("country") or "").strip()
    if not name:
        return {"urls": [], "msg": "Enter a station name first."}

    params = {
        "name": name,
        "limit": 10,
        "order": "votes",
        "reverse": "true",
        "hidebroken": "false",
    }
    if country:
        params["countrycode"] = country

    rows = []
    try:
        rows = rb("stations/search", params)
    except Exception as e:
        return {"urls": [], "msg": f"Lookup failed: {e}"}

    # Also try a tag search, in case the station name is generic.
    try:
        rows = rows + rb("stations/search", {**params, "name": "", "tagList": name})
    except Exception:
        pass

    seen, urls = set(), []
    for s in rows:
        u = s.get("url_resolved") or s.get("url")
        if u and u not in seen:
            seen.add(u)
            urls.append({
                "url": u,
                "name": (s.get("name") or "").strip(),
                "country": s.get("country", ""),
                "state": s.get("state", ""),
                "codec": s.get("codec", ""),
                "bitrate": s.get("bitrate", 0),
            })
    if not urls:
        return {"urls": [], "msg": f"No streams found for “{name}”."}
    return {"urls": urls[:5], "msg": ""}


def build_dial(country, state):
    """Spread the region's most popular stations across the FM dial. Each gets a
    stable slot (from its name) at least 0.2 MHz from its neighbours and from your
    logbook, so scanning past them plays them one after another."""
    base = {"order": "votes", "reverse": "true", "hidebroken": "true"}
    if country:
        base["countrycode"] = country
    batches = ([{**base, "state": state, "limit": 60}] if state else []) + [{**base, "limit": 120}]
    rows, seen = [], set()
    for params in batches:
        try:
            data = rb("stations/search", params)
        except Exception:
            continue
        for s in data:
            url = s.get("url_resolved") or s.get("url")
            if url and (s.get("name") or "").strip() and url not in seen:
                seen.add(url)
                rows.append(s)
    with radio.lock:
        have_urls = {u for e in radio.log for u in e["urls"]}
        have_names = {e["name"].lower() for e in radio.log}
        taken = {int(round(e["freq"] * 10)) for e in radio.log}
    out = []
    for s in rows:
        url = s.get("url_resolved") or s.get("url")
        name = s["name"].strip()
        if url in have_urls or name.lower() in have_names:
            continue
        h = 0
        for ch in name:
            h = (h * 31 + ord(ch)) & 0xFFFFFFFF
        for k in range(206):
            slot = 875 + (h + k) % 206
            if not ({slot - 1, slot, slot + 1} & taken):
                taken.add(slot)
                out.append({"freq": round(slot / 10, 1), "name": name, "url": url,
                            "country": s.get("country", ""), "state": s.get("state", ""),
                            "codec": s.get("codec", ""), "bitrate": s.get("bitrate", 0),
                            "tags": ", ".join((s.get("tags") or "").split(",")[:3])})
                break
        if len(out) >= 100:
            break
    with radio.lock:
        radio.dial = out
    return out


def directory_api(route, q):
    if route == "/api/dial":
        return build_dial((q.get("country") or "").strip(), (q.get("state") or "").strip())
    if route == "/api/geolocate":
        return geolocate_api(q)
    if route == "/api/recommend":
        return recommend()
    if route == "/api/autofill":
        return autofill_stream(q)
    if route == "/api/countries":
        data = rb("countries", {"order": "stationcount", "reverse": "true", "hidebroken": "true"})
        return [{"name": c.get("name", ""), "code": c["iso_3166_1"],
                 "count": c.get("stationcount", 0)}
                for c in data if c.get("iso_3166_1")]
    if route == "/api/states":
        want = (q.get("country") or "").lower()
        data = rb("states", {"hidebroken": "true"})
        out = [{"name": x.get("name", ""), "count": x.get("stationcount", 0)} for x in data
               if (x.get("country") or "").lower() == want and x.get("name")]
        return sorted(out, key=lambda x: -x["count"])[:400]
    try:
        offset = max(0, int(q.get("offset", 0) or 0))
    except (ValueError, TypeError):
        offset = 0
    name = (q.get("name") or "").strip()
    state = (q.get("state") or "").strip()
    country = (q.get("country") or "").strip()
    tags = (q.get("tags") or "").strip()
    hide_broken = str(q.get("hidebroken", "")).lower() in ("1", "true", "yes")
    base = {"order": "votes", "reverse": "true", "limit": 100, "offset": offset,
            "hidebroken": "true" if hide_broken else "false"}
    if country:
        base["countrycode"] = country
    queries = []
    if name:
        if state:
            queries.append({**base, "name": name, "state": state})
        queries.append({**base, "name": name})
        queries.append({**base, "tagList": name})
    elif tags:
        queries.append({**base, "tagList": tags})
    elif state:
        queries.append({**base, "state": state})
        queries.append({**base, "name": state})
    else:
        queries.append(base)
    rows, seen = [], set()
    for params in queries:
        try:
            for s in rb("stations/search", params):
                url = s.get("url_resolved") or s.get("url")
                if url and url not in seen:
                    seen.add(url)
                    rows.append(s)
        except Exception:
            continue
    return [{"name": (s.get("name") or "").strip(),
             "url": s.get("url_resolved") or s.get("url"),
             "country": s.get("country", ""), "state": s.get("state", ""),
             "codec": s.get("codec", ""), "bitrate": s.get("bitrate", 0),
             "tags": ", ".join((s.get("tags") or "").split(",")[:3])}
            for s in rows if (s.get("url_resolved") or s.get("url"))]


def recommend():
    """Suggest new stations from the tags of what you favourite and listen to."""
    weights = {}
    log = radio.snapshot()
    for e in log:
        w = e.get("secs", 0) / 60 + (30 if e.get("fav") else 0)
        for t in e.get("tags", []):
            weights[t] = weights.get(t, 0) + w
    weights = {t: w for t, w in weights.items() if w > 0}
    if not weights:
        return {"items": [], "msg": "Listen to a few stations or ★ some favourites and "
                                    "I'll start suggesting new ones."}
    top = sorted(weights, key=weights.get, reverse=True)[:3]
    cached = _rec_cache.get(tuple(top))
    if cached and time.time() - cached[0] < 300:
        return cached[1]
    have_urls = {u for e in log for u in e["urls"]}
    have_names = {e["name"].lower() for e in log}
    cand = {}
    for tag in top:
        try:
            rows = rb("stations/search", {"tag": tag, "tagExact": "true", "hidebroken": "true",
                                          "order": "votes", "reverse": "true", "limit": 25})
        except Exception:
            continue
        for s in rows:
            url = s.get("url_resolved") or s.get("url")
            name = (s.get("name") or "").strip()
            if not url or url in have_urls or name.lower() in have_names:
                continue
            tags = [x.strip().lower() for x in (s.get("tags") or "").split(",") if x.strip()]
            match = sorted((x for x in tags if x in weights), key=weights.get, reverse=True)
            score = sum(weights[x] for x in match) + min(s.get("votes", 0), 1000) / 1000 \
                + (2 if s.get("countrycode") == "GB" else 0)
            cand[url] = {"name": name, "url": url, "country": s.get("country", ""),
                         "state": s.get("state", ""), "codec": s.get("codec", ""),
                         "bitrate": s.get("bitrate", 0), "tags": ", ".join(tags[:3]),
                         "why": "Because you like " + " & ".join(match[:2]), "score": score}
    items = sorted(cand.values(), key=lambda x: -x["score"])[:6]
    out = {"items": items, "msg": "" if items else "Nothing new to suggest right now."}
    _rec_cache[tuple(top)] = (time.time(), out)
    return out


def open_stream(name, urls, _depth=0):
    """Open a station's stream from the server side (so the browser never has to
    deal with certificates/CORS). Returns an HTTP response object or None."""
    cached = _good_url.get(name)
    order = ([(cached[0], cached[1])] if cached else []) + \
            [(u, False) for u in urls if not cached or u != cached[0]]
    for url, insecure in order:
        for ins in ((True,) if insecure else (False, True)):
            ctx = ssl.create_default_context()
            if ins:
                ctx.check_hostname = False
                ctx.verify_mode = ssl.CERT_NONE
            try:
                resp = urllib.request.urlopen(
                    urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"}),
                    timeout=6, context=ctx)
            except Exception:
                continue
            kind = resp.headers.get_content_type()
            if kind.startswith("text/") or kind in _PLAYLIST_TYPES:
                inner = _playlist_url(resp.read(16384).decode("utf-8", "replace"))
                resp.close()
                if inner and _depth < 2:
                    nxt = open_stream(name, [inner], _depth + 1)
                    if nxt:
                        return nxt
                break          # a web page, not audio - don't try the insecure retry
            return resp
    return None


class ReusableHTTPServer(ThreadingHTTPServer):
    allow_reuse_address = True


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _ok(self):
        host = self.headers.get("Host", "").split(":")[0]
        origin = self.headers.get("Origin")
        good = {f"http://127.0.0.1:{PORT}", f"http://localhost:{PORT}"}
        return host in ("127.0.0.1", "localhost") and (origin is None or origin in good)

    def _send(self, body, ctype, code=200):
        data = body if isinstance(body, bytes) else body.encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _stream(self, q):
        """Relay a logged station's audio to the browser (used for scan previews)."""
        try:
            f = round(float(q.get("freq", 0)), 1)
        except ValueError:
            return self._send("bad request", "text/plain", 400)
        with radio.lock:
            e = next((x for x in radio.log if abs(x["freq"] - f) <= 0.05), None)
            if e:
                name, urls = e["name"], list(e["urls"])
            else:
                d = next((x for x in radio.dial if abs(x["freq"] - f) <= 0.05), None)
                name, urls = (d["name"], [d["url"]]) if d else ("", [])
        resp = open_stream(name, urls) if urls else None
        if not resp:
            return self._send("no stream", "text/plain", 502)
        try:
            self.send_response(200)
            self.send_header("Content-Type", resp.headers.get("Content-Type", "audio/mpeg"))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            read = getattr(resp, "read1", resp.read)
            while True:
                chunk = read(8192)
                if not chunk:
                    break
                self.wfile.write(chunk)
        except OSError:
            pass
        finally:
            resp.close()

    def do_GET(self):
        if not self._ok():
            return self._send("forbidden", "text/plain", 403)
        u = urlsplit(self.path)
        q = {k: v[0] for k, v in parse_qs(u.query).items()}
        if u.path == "/":
            self._send(PAGE, "text/html; charset=utf-8")
        elif u.path == "/api/state":
            self._send(json.dumps(radio.state()), "application/json")
        elif u.path == "/api/stream":
            self._stream(q)
        elif u.path in ("/api/countries", "/api/states", "/api/directory",
                        "/api/recommend", "/api/geolocate", "/api/autofill", "/api/dial"):
            try:
                self._send(json.dumps(directory_api(u.path, q)), "application/json")
            except Exception as e:
                self._send(json.dumps({"error": str(e)}), "application/json", 502)
        else:
            self._send("not found", "text/plain", 404)

    def do_POST(self):
        if not self._ok():
            return self._send("forbidden", "text/plain", 403)
        try:
            body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")
            if self.path == "/api/tune":
                radio.tune(min(108.0, max(87.5, round(float(body["freq"]), 1))))
            elif self.path == "/api/play":
                radio.play_url(str(body["name"])[:80], str(body["url"]))
            elif self.path == "/api/volume":
                radio.set_vol(body["level"])
            elif self.path == "/api/hush":
                radio.hush()
            elif self.path == "/api/stop":
                radio.stop()
            elif self.path == "/api/log":
                radio.edit(body)
                threading.Thread(target=prewarm, daemon=True).start()
        except (ValueError, KeyError, TypeError):
            return self._send("bad request", "text/plain", 400)
        self._send(json.dumps(radio.state()), "application/json")


PAGE = r"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Local FM Tuner</title>
<style>
:root{color-scheme:dark;--bg:#110b06;--wood1:#4b2f1b;--wood2:#2a190e;--panel:#1a1109;--line:#4d3722;--cream:#f3e7c9;--ink:#f3e7c9;--mute:#b9a579;--brass:#d4a94f;--glow:#ffb347;--green:#65d685;--red:#e0523f}
*{box-sizing:border-box}
body{margin:0;min-height:100vh;display:flex;justify-content:center;padding:clamp(10px,3vw,28px);color:var(--ink);
background:radial-gradient(1200px 600px at 50% -10%,#3a2415 0,transparent 70%),var(--bg);font:15px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
.radio{width:min(1040px,100%);padding:clamp(14px,3vw,26px);border-radius:26px;border:2px solid #6b4526;
background:repeating-linear-gradient(95deg,#ffffff06 0 2px,transparent 2px 7px),linear-gradient(160deg,var(--wood1),var(--wood2));
box-shadow:0 30px 80px #000c,inset 0 1px 0 #ffffff1a,inset 0 0 40px #0006}
.topbar{display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:12px;margin-bottom:18px}
.brand{display:flex;align-items:center;gap:12px}
h1{margin:0;font-size:13px;font-weight:700;letter-spacing:.28em;color:var(--brass);text-shadow:0 1px 0 #000}
h2{font-size:17px;margin:0 0 12px;color:var(--brass);display:flex;align-items:center;gap:10px;flex-wrap:wrap}
.led{width:12px;height:12px;border-radius:50%;background:#3a2a1c;border:1px solid #000;box-shadow:inset 0 1px 2px #0008;transition:.3s}
body[data-state=playing] .led{background:var(--green);box-shadow:0 0 10px var(--green),0 0 2px #fff8 inset}
body[data-state=tuning] .led{background:var(--glow);box-shadow:0 0 10px var(--glow);animation:pulse 1s infinite}
body[data-state=error] .led{background:var(--red);box-shadow:0 0 10px var(--red)}
@keyframes pulse{50%{opacity:.35}}
.locbox{display:flex;align-items:center;gap:8px;font-size:13px;background:var(--panel);border:1px solid var(--line);padding:5px 6px 5px 12px;border-radius:999px;color:#e9c987}
.panel{display:grid;grid-template-columns:1fr 240px;gap:24px;align-items:center}
@media(max-width:760px){.panel{grid-template-columns:1fr}}
.window{background:linear-gradient(#150d07,#1d1209);border:2px solid var(--brass);border-radius:16px;padding:18px;box-shadow:inset 0 0 30px #000a,0 0 0 4px #00000055}
.lcd{font:700 clamp(46px,9vw,68px)/1 ui-monospace,"SF Mono",Menlo,Consolas,monospace;font-variant-numeric:tabular-nums;color:var(--glow);text-shadow:0 0 18px #ff9a1f99,0 0 3px #ffd08a}
.lcd small{font-size:16px;color:#b97a2a;margin-left:10px;letter-spacing:.1em}
#status{min-height:30px;margin:10px 0 14px;padding:5px 12px;display:inline-block;border-radius:999px;background:#ffffff0d;border:1px solid #ffffff14;color:#f0d9a0;font-size:14px;max-width:100%}
.scale{position:relative;display:block;height:78px;border-radius:8px;overflow:hidden;cursor:pointer;border:1px solid #000;
background:linear-gradient(#f8ecc8,#d9c288 70%,#c9ad6a);box-shadow:inset 0 3px 8px #0005,inset 0 -2px 6px #0003}
.tick{position:absolute;top:0;width:1px;background:#5a4220}
.lab{position:absolute;top:36px;font-size:10px;font-weight:600;color:#3a2a12;transform:translateX(-50%)}
.mark{position:absolute;bottom:3px;transform:translateX(-50%);font-size:9px;font-weight:700;color:#8a1f12;white-space:nowrap}
.vmark{position:absolute;bottom:0;width:2px;height:9px;background:#8a1f12;opacity:.45;transform:translateX(-50%)}
#needle{position:absolute;top:0;bottom:0;width:2px;margin-left:-1px;background:#e5261c;box-shadow:0 0 8px #f00,0 0 2px #fff6;pointer-events:none}
#needle::before{content:"";position:absolute;top:0;left:-4px;border:5px solid transparent;border-top-color:#e5261c}
.ctl{display:flex;gap:10px 18px;align-items:center;margin-top:16px;font-size:13px;flex-wrap:wrap;color:var(--mute)}
.ctl label{display:flex;align-items:center;gap:6px;cursor:pointer}
.presets{display:flex;flex-wrap:wrap;gap:8px;margin-top:14px}
.presets button{border-radius:999px;padding:5px 12px;font-size:13px}
.presets button small{opacity:.7;margin-left:4px}
.presets button.on{background:var(--glow);color:#2a1700;border-color:var(--glow)}
.knobwrap{text-align:center}
#knob{width:clamp(150px,34vw,190px);aspect-ratio:1;border-radius:50%;margin:auto;position:relative;touch-action:none;cursor:grab;border:3px solid #1c1208;
background:repeating-conic-gradient(#7d6126 0 3deg,#b8943f 3deg 6deg);box-shadow:0 12px 26px #000b,0 0 0 6px #00000040,inset 0 0 14px #0008}
#knob:active{cursor:grabbing}
#knob::before{content:"";position:absolute;inset:13%;border-radius:50%;background:radial-gradient(circle at 35% 28%,#f1d58a,#a47f2c 55%,#5a4414);box-shadow:inset 0 -6px 12px #0006,0 2px 6px #0008}
#knob::after{content:"";position:absolute;left:50%;top:7%;width:6px;height:15%;margin-left:-3px;background:#1b120b;border-radius:3px;z-index:1}
.hint{font-size:12px;color:var(--mute);margin-top:12px;line-height:1.4}
button{font:inherit;font-size:13px;background:linear-gradient(#6a4524,#4f3319);color:var(--cream);border:1px solid #8a6a32;border-radius:8px;padding:5px 12px;cursor:pointer;transition:filter .15s,transform .05s}
button:hover{filter:brightness(1.2)}button:active{transform:translateY(1px)}
button:focus-visible,input:focus-visible,select:focus-visible,summary:focus-visible,#knob:focus-visible{outline:2px solid var(--glow);outline-offset:2px}
button.logged{background:#213a24;border-color:var(--green);color:var(--green)}
#off{border-color:#a8473a;color:#ffb8aa}
td button[data-s]{background:none;border:0;font-size:20px;color:var(--brass);padding:0 4px}
.tabs{display:flex;gap:4px;margin:26px 0 16px;border-bottom:1px solid var(--line)}
.tabs button{background:none;border:0;border-bottom:3px solid transparent;border-radius:0;padding:10px 16px;font-size:14px;color:var(--mute)}
.tabs button.on{color:var(--glow);border-bottom-color:var(--glow)}
.tab{display:none;overflow-x:auto}.tab.on{display:block}
table{width:100%;border-collapse:collapse;background:var(--panel);border-radius:12px;overflow:hidden;border:1px solid var(--line)}
th,td{padding:9px 11px;text-align:left;border-bottom:1px solid #33241580;font-size:14px}
th{color:var(--brass);font-size:11px;text-transform:uppercase;letter-spacing:.1em;background:#ffffff08}
tbody tr:hover{background:#ffffff08}
td.f{font:700 15px ui-monospace,Menlo,Consolas,monospace;color:var(--glow)}
tr.on{background:#4a3014!important;box-shadow:inset 3px 0 0 var(--glow)}
td input,.add input,.dirbar input,.dirbar select{background:#0d0804;color:var(--cream);border:1px solid var(--line);border-radius:8px;padding:7px 9px;width:100%;min-width:0;font:inherit;font-size:14px}
.add{display:grid;grid-template-columns:110px 1fr 1.5fr auto 1fr auto;gap:8px;margin-top:12px}
@media(max-width:760px){.add{grid-template-columns:1fr 1fr}}
summary{cursor:pointer;color:var(--brass);margin-top:14px;font-size:14px}
.dirbar{display:grid;grid-template-columns:2fr 1.3fr 1.3fr auto;gap:8px;margin-bottom:10px}
@media(max-width:760px){.dirbar{grid-template-columns:1fr 1fr}}
.tags{color:#a99468;font-size:12px;max-width:220px}
#dir td{vertical-align:middle}
.recitem{display:flex;justify-content:space-between;align-items:center;gap:12px;background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:10px 14px;margin-bottom:8px}
.recitem .hint{margin:2px 0 0}
#vol{width:130px;vertical-align:middle;accent-color:var(--glow)}
@media(prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important}}
</style></head><body><div class="radio">
<div class="topbar">
 <div class="brand"><span class="led"></span><h1 id="rtitle">📻 SOUTHEND &amp; ESSEX FM TUNER</h1></div>
 <div class="locbox">
  <span id="locstatus">📍 Detecting your location…</span>
  <button id="locbtn" title="Ask browser for your current location">📍 Locate Me</button>
 </div>
</div>
<div class="panel">
 <div class="window">
  <div class="lcd"><span id="freq">97.5</span><small>MHz FM</small></div>
  <div id="status">Turn the knob to tune in</div>
  <div class="scale" id="scale"><div id="needle"></div></div>
  <div class="ctl"><button id="off">⏻ Off</button>
   <span>🔊 <input type="range" id="vol" min="0" max="100" value="50"> <span id="volv">50%</span></span>
   <label><input type="checkbox" id="hiss" checked> Static between stations</label>
   <label><input type="checkbox" id="scanon" checked> Hear stations while scanning</label></div>
  <div class="presets" id="presets"></div>
 </div>
 <div class="knobwrap"><div id="knob" title="Drag to tune"></div>
  <div class="hint">Drag the knob · mouse wheel · ← → keys (Shift = 1 MHz) — stations fade in as you pass them</div></div>
</div>
<nav class="tabs"><button class="on" data-tab="t-log">📒 Logbook</button><button data-tab="t-rec">✨ For you</button><button data-tab="t-dir">🌍 Directory</button></nav>
<section class="tab on" id="t-log">
<h2><span id="logtitle">📒 FM Logbook — Southend &amp; Essex</span>
 <label style="font-size:12px;font-weight:400;margin-left:12px"><input type="checkbox" id="favonly"> ★ favourites only</label></h2>
<table id="log"><thead><tr><th>★</th><th>MHz</th><th>Station</th><th>Listened</th><th>Last heard</th><th>Notes</th><th></th></tr></thead><tbody></tbody></table>
<details><summary>+ Log a new station (leave MHz blank to auto-assign)</summary><div class="add">
 <input id="nf" type="number" step="0.1" min="87.5" max="108" placeholder="Auto MHz">
 <input id="nn" placeholder="Station name">
 <input id="nu" placeholder="Stream URL (optional)">
 <button id="nauto" style="white-space:nowrap">🔍 Auto-find</button>
 <input id="nt" placeholder="Notes"><button id="na">Add</button></div></details>

</section>
<section class="tab" id="t-rec">
<h2>✨ Recommended for you <button id="recgo" style="font-size:12px;margin-left:10px">↻ Refresh</button></h2>
<div id="rec" class="hint">Loading…</div>

</section>
<section class="tab" id="t-dir">
<h2>🌍 Station Directory — search every region</h2>
<div class="dirbar"><input id="dq" placeholder="Search by name or genre…"><select id="dc"></select>
 <input id="ds" list="dsl" placeholder="Region / county (e.g. Essex)"><datalist id="dsl"></datalist><button id="dgo">Search</button></div>
<div style="display:flex;align-items:center;gap:12px;margin-bottom:4px">
 <div id="dmsg" class="hint" style="flex:1;margin:0"></div>
 <label class="hint" style="margin:0;font-size:12px;white-space:nowrap">
  <input type="checkbox" id="dhb"> Hide offline stations</label>
</div>
<table id="dir"><thead><tr><th>Station</th><th>Region</th><th>Format</th><th>Tags</th><th></th></tr></thead><tbody></tbody></table>
<button id="dmore" style="display:none;margin-top:10px">Load more</button>
</section>
<audio id="bplayer" style="display:none"></audio>
</div>
<script>
const MIN=87.5,MAX=108.0,SPAN=270,$=id=>document.getElementById(id);
const fToA=f=>(f-MIN)/(MAX-MIN)*SPAN-SPAN/2, aToF=a=>MIN+(a+SPAN/2)/SPAN*(MAX-MIN);
const clampF=f=>Math.min(MAX,Math.max(MIN,Math.round(f*10)/10));
let freq=97.5,angle=fToA(97.5),timer,st={log:[],status:'off'},drag=null,lastKey='',first=true,ac,ng;
let dirOff=0,dirTimer,volT,shownUrls=new Set();
let tuneLast=0,tuneSent=null,settle=null,pollT=null;
const TUNE_MIN=110,TUNE_SETTLE=80;
const bplayer=$('bplayer');

const esc=s=>String(s||'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmt=s=>{s=Math.round(s||0);const h=Math.floor(s/3600),m=Math.floor(s%3600/60);return h?h+'h '+m+'m':m?m+'m':s+'s'};
const jget=async u=>{const r=await fetch(u);if(!r.ok)throw 0;return r.json()};
const post=(u,b)=>fetch(u,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(b||{})}).then(r=>r.json()).then(upd);
const inEditable=()=>{const ae=document.activeElement;return !!(ae&&ae.matches&&ae.matches('td input,INPUT,TEXTAREA,SELECT'))};

function audio(){
 if(ac){ac.resume();return}
 ac=new AudioContext();
 const n=ac.sampleRate*2,b=ac.createBuffer(1,n,ac.sampleRate),d=b.getChannelData(0);
 for(let i=0;i<n;i++)d[i]=Math.random()*2-1;
 const s=ac.createBufferSource();s.buffer=b;s.loop=true;
 ng=ac.createGain();ng.gain.value=0;s.connect(ng).connect(ac.destination);s.start();hissLevel();
}
function hissLevel(){if(ng)ng.gain.value=((st.status==='off'||st.status==='playing'||!$('hiss').checked)?0:0.035)*(1-maxG)}
function show(){$('freq').textContent=freq.toFixed(1);$('knob').style.transform='rotate('+angle+'deg)';$('needle').style.left=((freq-MIN)/(MAX-MIN)*100)+'%'}

// ---- scan previews: stations near the needle are streamed into the page and
// ---- faded in/out by distance, so you hear each one as you scroll past ----
let prev={},maxG=0,scanning=false,scanMode=false,handT=null,scanEndT=null,deadUntil={};
let dialList=[];
const REACH=0.3,PRELOAD=0.8,MAXPREV=8,SCAN_SETTLE=320;
// every station on the dial: your logbook plus the region's stations in their own slots
function stations(){return st.log.concat(dialList.filter(d=>!st.log.some(l=>Math.abs(l.freq-d.freq)<0.05)).map(d=>({freq:d.freq,name:d.name,urls:[d.url]})))}
function drawDial(){document.querySelectorAll('.vmark').forEach(m=>m.remove());
 dialList.forEach(d=>{const m=document.createElement('div');m.className='vmark';m.title=d.name;m.style.left=((d.freq-MIN)/(MAX-MIN)*100)+'%';$('scale').appendChild(m)})}
async function loadDial(){try{dialList=await jget('/api/dial?country='+encodeURIComponent($('dc').value)+'&state='+encodeURIComponent($('ds').value));drawDial();previewUpdate()}catch(e){}}
let dialKey='';setInterval(()=>{const k=$('dc').value+'|'+$('ds').value;if(k!==dialKey){dialKey=k;loadDial()}},1500);
function startPrev(e){
 if(Object.keys(prev).length>=MAXPREV)return null;
 const el=new Audio();el.src='/api/stream?freq='+e.freq;
 const g=ac.createGain();g.gain.value=0;
 try{ac.createMediaElementSource(el).connect(g);g.connect(ac.destination)}catch(x){return null}
 el.onerror=()=>{deadUntil[e.freq]=performance.now()+30000;stopPrev(e.freq)};
 el.play().catch(()=>{});
 return prev[e.freq]={el,g,t:performance.now()};
}
function stopPrev(f){const p=prev[f];if(!p)return;p.el.onerror=null;p.el.pause();p.el.removeAttribute('src');p.el.load();try{p.g.disconnect()}catch(x){}delete prev[f]}
function endScan(){
 scanMode=false;maxG=0;clearTimeout(scanEndT);
 for(const f in prev)prev[f].g.gain.setTargetAtTime(0,ac.currentTime,0.12);
 clearTimeout(handT);handT=setTimeout(()=>{if(!scanMode)for(const f in prev)stopPrev(f)},700);
 hissLevel();
}
function previewUpdate(){
 if(!ac||!scanMode)return;
 if(!scanning&&['playing','error','off'].includes(st.status)){endScan();return}
 const now=performance.now();let mx=0;
 for(const e of stations()){
  if(!e.urls||!e.urls.length||(deadUntil[e.freq]||0)>now)continue;
  const d=Math.abs(e.freq-freq);let p=prev[e.freq];
  if(!p&&d<=PRELOAD)p=startPrev(e);
  if(!p)continue;
  const gn=d>=REACH?0:Math.pow(1-d/REACH,1.5);
  if(gn>0.02)p.t=now;
  mx=Math.max(mx,gn);
  p.g.gain.setTargetAtTime(gn,ac.currentTime,0.05);
 }
 for(const f in prev)if(now-prev[f].t>6000&&Math.abs(f-freq)>PRELOAD)stopPrev(f);
 maxG=mx;hissLevel();
}

function liveLabel(){const e=stations().find(x=>Math.abs(x.freq-freq)<=0.05);
 $('status').textContent=e?(e.urls&&e.urls.length?'🎶 '+e.name:'〰 '+e.name+' — no stream'):'〰 static'}
function sendTune(){
 clearTimeout(settle);settle=null;scanning=false;
 if(scanMode){clearTimeout(scanEndT);scanEndT=setTimeout(endScan,8000)}
 if(tuneSent===freq)return;
 tuneSent=freq;tuneLast=performance.now();
 fetch('/api/tune',{method:'POST',headers:{'Content-Type':'application/json'},
  body:JSON.stringify({freq})}).then(r=>r.json()).then(upd).catch(()=>{});
}
function arm(now){
 audio();
 const scan=$('scanon').checked&&!now;
 if(scan&&!scanning){
  scanning=true;scanMode=true;tuneSent=null;clearTimeout(handT);clearTimeout(scanEndT);
  if(st.status==='playing')fetch('/api/hush',{method:'POST'}).catch(()=>{});
 }
 st.status='tuning';document.body.dataset.state='tuning';hissLevel();show();liveLabel();render();
 clearTimeout(settle);
 if(scan){previewUpdate();settle=setTimeout(sendTune,SCAN_SETTLE)}
 else{settle=setTimeout(sendTune,TUNE_SETTLE);if(performance.now()-tuneLast>=TUNE_MIN)sendTune()}
}
function setFreq(f,now){freq=clampF(f);angle=fToA(freq);arm(now);if(now)sendTune()}

const ptr=e=>{const r=$('knob').getBoundingClientRect();return Math.atan2(e.clientY-(r.top+r.height/2),e.clientX-(r.left+r.width/2))*180/Math.PI};
$('knob').onpointerdown=e=>{$('knob').setPointerCapture(e.pointerId);drag={a:ptr(e)};audio()};
$('knob').onpointermove=e=>{if(!drag)return;const a=ptr(e);let d=a-drag.a;if(d>180)d-=360;if(d<-180)d+=360;drag.a=a;
 angle=Math.max(-SPAN/2,Math.min(SPAN/2,angle+d));freq=clampF(aToF(angle));arm()};
$('knob').onpointerup=$('knob').onpointercancel=()=>drag=null;
for(const el of [$('knob'),$('scale')])el.addEventListener('wheel',e=>{e.preventDefault();setFreq(freq+(e.deltaY<0?0.1:-0.1))},{passive:false});
$('scale').onclick=e=>{const r=$('scale').getBoundingClientRect();setFreq(MIN+(e.clientX-r.left)/r.width*(MAX-MIN))};
document.onkeydown=e=>{if(inEditable())return;const s=e.shiftKey?1:0.1;
 if(e.key==='ArrowRight'||e.key==='ArrowUp'){e.preventDefault();setFreq(freq+s)}
 if(e.key==='ArrowLeft'||e.key==='ArrowDown'){e.preventDefault();setFreq(freq-s)}};
$('off').onclick=()=>{clearTimeout(timer);clearTimeout(settle);tuneSent=null;bplayer.pause();bplayer.src='';scanning=false;if(scanMode)endScan();post('/api/stop')};
$('hiss').onchange=hissLevel;
$('na').onclick=()=>{
 if(!$('nn').value.trim())return;
 const f=parseFloat($('nf').value);
 post('/api/log',{op:'add',freq:f||'auto',name:$('nn').value,url:$('nu').value,note:$('nt').value});
 ['nf','nn','nu','nt'].forEach(i=>$(i).value='');
};
$('nauto').onclick=async()=>{
 const name=$('nn').value.trim();
 if(!name){$('status').textContent='⚠ Enter a station name first';return}
 $('status').textContent='🔍 Searching Radio Browser…';
 try{
  const d=await jget('/api/autofill?name='+encodeURIComponent(name));
  if(!d.urls||!d.urls.length){$('status').textContent='⚠ '+(d.msg||'No streams found');return}
  const u=d.urls[0];
  $('nu').value=u.url;
  $('status').textContent='✓ Found: '+u.name+' ('+u.codec+' '+(u.bitrate||'')+' kbps) — press Add';
 }catch(e){$('status').textContent='⚠ Lookup failed — check connection'}
};

function upd(s){
 st=s;if(first){first=false;freq=s.freq;angle=fToA(freq)}
 const m={off:'⏻ '+s.msg,tuning:'⏳ Tuning…',playing:'🎶 '+s.station+' — '+s.msg,static:'〰 '+s.msg,error:'⚠ '+s.msg};
 if((!drag&&!timer&&!settle)||s.status!=='tuning')$('status').textContent=m[s.status]||s.msg;
 if(s.browser_url){
  if(bplayer.src!==s.browser_url){bplayer.src=s.browser_url;bplayer.play().catch(()=>{})}
 }else if(!bplayer.paused){
  bplayer.pause();bplayer.src='';
 }
 if(document.activeElement!==$('vol')){
  if(s.volume!=null){$('vol').value=s.volume;$('volv').textContent=s.volume+'%'}
 }
 hissLevel();show();render();previewUpdate();
 document.body.dataset.state=s.status;renderPresets();
}

function buildScale(){const sc=$('scale');for(let f=88;f<=108;f++){const t=document.createElement('div');t.className='tick';
 t.style.left=((f-MIN)/(MAX-MIN)*100)+'%';t.style.height=f%2?'18px':'30px';sc.appendChild(t);
 if(f%2===0){const l=document.createElement('div');l.className='lab';l.style.left=t.style.left;l.textContent=f;sc.appendChild(l)}}}

function render(){
 const marks=document.querySelectorAll('.mark');marks.forEach(m=>m.remove());
 st.log.forEach(e=>{const m=document.createElement('div');m.className='mark';m.style.left=((e.freq-MIN)/(MAX-MIN)*100)+'%';m.textContent='▲ '+e.name.split(' ')[0];$('scale').appendChild(m)});
 const key=JSON.stringify(st.log.map(e=>[e.freq,e.name,e.fav,e.heard,Math.floor((e.secs||0)/60),e.last,e.note,e.urls.length]))+$('favonly').checked;
 if(key===lastKey){
  document.querySelectorAll('#log tbody tr').forEach(tr=>{
   const c=tr.querySelector('td.f');
   if(c)tr.classList.toggle('on',Math.abs(parseFloat(c.textContent)-freq)<=0.05);
  });
  return;
 }
 if(inEditable())return;
 lastKey=key;
 const tb=document.querySelector('#log tbody');tb.innerHTML='';
 st.log.filter(e=>!$('favonly').checked||e.fav).sort((a,b)=>a.freq-b.freq).forEach(e=>{
  const tr=document.createElement('tr');if(Math.abs(e.freq-freq)<=0.05)tr.className='on';
  tr.innerHTML='<td><button data-s="'+e.freq+'" title="Favourite">'+(e.fav?'★':'☆')+'</button></td><td class="f">'+e.freq.toFixed(1)+'</td><td>'+esc(e.name)+(e.urls.length?'':' <i>(no stream)</i>')+'</td><td>'+(e.heard?'✔ ×'+e.heard+' · '+fmt(e.secs):'—')+
  '</td><td>'+esc(e.last||'')+'</td><td><input value="'+esc(e.note||'')+'" data-n="'+e.freq+'"></td><td><button data-t="'+e.freq+'">Tune</button> <button data-d="'+e.freq+'" title="Remove">✕</button></td>';
  tb.appendChild(tr);
 });
 updateLogButtons();
}

function getAutoFreq(r){
 const have=st.log.find(e=>e.urls.includes(r.url)||e.name.toLowerCase()===r.name.toLowerCase());
 if(have)return {freq:have.freq,auto:false,have:true};
 const dv=dialList.find(d=>d.url===r.url||d.name.toLowerCase()===r.name.toLowerCase());
 if(dv&&!st.log.some(e=>Math.abs(e.freq-dv.freq)<0.05))return {freq:dv.freq,auto:false,have:false};
 const m=(r.name+' '+(r.tags||'')).match(/\b(8[7-9]|9\d|10[0-8])\.\d\b/);
 if(m){
  const g=parseFloat(m[0]);
  if(g>=87.5&&g<=108&&!st.log.some(e=>Math.abs(e.freq-g)<0.05))return {freq:g,auto:false,have:false};
 }
 let h=0;for(const c of r.name)h=(h*31+c.charCodeAt(0))>>>0;
 for(let k=0;k<206;k++){
  const c=Math.round((87.5+((h+k)%206)/10)*10)/10;
  if(!st.log.some(e=>Math.abs(e.freq-c)<0.15))return {freq:c,auto:true,have:false};
 }
 return {freq:87.5,auto:true,have:false};
}

function logDir(r){
 const where=[r.state,r.country].filter(Boolean).join(', ');
 const {freq:f,auto,have}=getAutoFreq(r);
 return post('/api/log',{
  op:'add',
  freq:f,
  name:r.name,
  url:r.url,
  tags:r.tags,
  note:(auto?'Auto-assigned dial spot · ':'')+where
 }).then(()=>{
  $('status').textContent='📒 Logged '+r.name+' on '+f.toFixed(1)+' MHz FM';
  return f;
 });
}

function playDir(r){
 const {freq:f,have}=getAutoFreq(r);
 freq=clampF(f);angle=fToA(freq);st.status='tuning';clearTimeout(timer);hissLevel();show();$('status').textContent='⏳ Tuning…';
 const go=()=>{tuneSent=freq;return post('/api/tune',{freq})};
 if(have)go();else logDir(r).then(go);
}

function updateLogButtons(){
 document.querySelectorAll('#dir tbody tr, #rec .recitem').forEach(el=>{
  if(!el.dataset.r)return;
  const r=JSON.parse(el.dataset.r),btn=el.querySelector('button[data-l]');
  if(!btn)return;
  const ex=st.log.find(e=>e.urls.includes(r.url)||e.name.toLowerCase()===r.name.toLowerCase());
  if(ex){btn.className='logged';btn.textContent='✔ '+ex.freq.toFixed(1)+' FM'}
  else{btn.className='';btn.textContent='＋ Log'}
 });
}

document.querySelector('#log tbody').addEventListener('click',e=>{const t=e.target.dataset;
 if(t.t)setFreq(parseFloat(t.t),true);if(t.s)post('/api/log',{op:'fav',freq:parseFloat(t.s)}).then(loadRec);if(t.d&&confirm('Remove this station from the logbook?'))post('/api/log',{op:'del',freq:parseFloat(t.d)})});
document.querySelector('#log tbody').addEventListener('change',e=>{if(e.target.dataset.n)post('/api/log',{op:'note',freq:parseFloat(e.target.dataset.n),note:e.target.value})});

$('vol').oninput=()=>{
 $('volv').textContent=$('vol').value+'%';
 bplayer.volume=$('vol').value/100;
 clearTimeout(volT);volT=setTimeout(()=>post('/api/volume',{level:+$('vol').value}),120); };
$('favonly').onchange=render;

async function loadRec(){
 $('rec').className='hint';$('rec').textContent='Finding stations you might like…';
 try{
  const d=await jget('/api/recommend');
  if(!d.items||!d.items.length){$('rec').textContent=d.msg||'Nothing new to suggest right now.';return}
  $('rec').className='';$('rec').innerHTML='';
  d.items.forEach(r=>{
   const div=document.createElement('div');div.className='recitem';div.dataset.r=JSON.stringify(r);
   div.innerHTML='<div><b>'+esc(r.name)+'</b><div class="hint">'+esc(r.why)+' · '+esc([r.state,r.country].filter(Boolean).join(', '))+'</div></div>'+
    '<div><button data-p="1">▶ Play</button> <button data-l="1">＋ Log</button></div>';
   $('rec').appendChild(div);
  });
  updateLogButtons();
 }catch(e){$('rec').textContent='⚠ Recommendations unavailable right now.'}
}
$('rec').addEventListener('click',e=>{ const d=e.target.closest('.recitem');if(!d)return; const r=JSON.parse(d.dataset.r); if(e.target.dataset.p){audio();playDir(r)} if(e.target.dataset.l){logDir(r)} });
$('recgo').onclick=loadRec;

async function loadRegions(){
 try{
  const cs=await jget('/api/countries'),sel=$('dc');
  sel.innerHTML='<option value="">🌍 All countries</option>'+cs.map(c=>'<option value="'+esc(c.code)+'" data-n="'+esc(c.name)+'">'+esc(c.name)+' ('+c.count+')</option>').join('');
  sel.value='GB';
  await loadStates();
 }catch(e){$('dmsg').textContent='⚠ Directory unavailable (check your connection).'}
}

async function loadStates(){
 const o=$('dc').selectedOptions[0];$('dsl').innerHTML='';if(!o||!o.dataset.n)return;
 try{
  const ss=await jget('/api/states?country='+encodeURIComponent(o.dataset.n));
  $('dsl').innerHTML=ss.map(s=>'<option value="'+esc(s.name)+'">'+s.count+' stations</option>').join('');
 }catch(e){}
}

async function dirSearch(more){
 if(more){dirOff+=100}else{dirOff=0;shownUrls.clear()}
 $('dmsg').textContent='Searching…';
 const q=new URLSearchParams({name:$('dq').value,country:$('dc').value,state:$('ds').value,
  offset:dirOff,hidebroken:$('dhb').checked?'true':'false'});
 try{
  const rows=await jget('/api/directory?'+q),tb=document.querySelector('#dir tbody');
  if(!more)tb.innerHTML='';
  let added=0;
  rows.forEach(r=>{
   if(shownUrls.has(r.url))return;
   shownUrls.add(r.url);added++;
   const tr=document.createElement('tr');tr.dataset.r=JSON.stringify(r);
   tr.innerHTML='<td>'+esc(r.name)+'</td><td>'+esc([r.state,r.country].filter(Boolean).join(', '))+'</td><td>'+esc(r.codec||'')+' '+(r.bitrate||'')+
   '</td><td class="tags">'+esc(r.tags||'')+'</td><td><button data-p="1">▶ Play</button> <button data-l="1">＋ Log</button></td>';
   tb.appendChild(tr);
  });
  updateLogButtons();
  const n=shownUrls.size,pl=n===1?'':'s';
  if(rows.length>=100){$('dmsg').textContent=added?('Showing '+n+' station'+pl):'No more results — try different search terms.';}
  else{$('dmsg').textContent=n?('Showing '+n+' station'+pl):'No stations found.';}
  $('dmore').style.display=(rows.length>=100&&added)?'':'none';
 }catch(e){$('dmsg').textContent='⚠ Directory unavailable (check your connection).'}
}

document.querySelector('#dir tbody').addEventListener('click',e=>{
 const tr=e.target.closest('tr'),t=e.target.dataset;if(!tr)return;
 const r=JSON.parse(tr.dataset.r);
 if(t.p){audio();playDir(r)}
 if(t.l){logDir(r)}
});

async function applyLocation(params){
 try{
  const loc=await jget('/api/geolocate?'+new URLSearchParams(params));
  const place=[loc.city,loc.state,loc.countrycode].filter(Boolean).join(', ');
  $('locstatus').textContent=place?('📍 '+place):'📍 Location detected';
  if(loc.city||loc.state){
   const area=[loc.city,loc.state].filter(Boolean).join(' & ');
   $('rtitle').textContent='📻 '+area.toUpperCase()+' FM TUNER';
   $('logtitle').textContent='📒 FM Logbook — '+area;
  }
  if(loc.countrycode&&$('dc').querySelector('option[value="'+loc.countrycode+'"]')){
   $('dc').value=loc.countrycode;
   await loadStates();
  }
  if(loc.state){
   $('ds').value=loc.state;
  }
  dirSearch();
 }catch(e){
  $('locstatus').textContent='📍 Could not resolve location';
 }
}

function askLocation(){
 if(!navigator.geolocation){
  $('locstatus').textContent='📍 Geolocation not supported — using IP location…';
  applyLocation({});
  return;
 }
 $('locstatus').textContent='📍 Please allow location access in your browser…';
 navigator.geolocation.getCurrentPosition(
  pos=>{
   applyLocation({lat:pos.coords.latitude.toFixed(5),lon:pos.coords.longitude.toFixed(5)});
  },
  err=>{
   $('locstatus').textContent='📍 Browser location denied — using approximate IP location…';
   applyLocation({});
  },
  {enableHighAccuracy:false,timeout:10000,maximumAge:300000}
 );
}

$('locbtn').onclick=askLocation;
$('dgo').onclick=()=>dirSearch();
$('dmore').onclick=()=>dirSearch(true);
$('dhb').onchange=()=>dirSearch();
$('dq').oninput=()=>{clearTimeout(dirTimer);dirTimer=setTimeout(()=>dirSearch(),450)};
$('ds').onchange=()=>dirSearch();
$('dc').onchange=()=>{$('ds').value='';loadStates();dirSearch()};
for(const i of ['dq','ds'])$(i).onkeydown=e=>{if(e.key==='Enter')dirSearch()};

// ---- tabs + favourite presets ----
document.querySelectorAll('.tabs button').forEach(b=>b.onclick=()=>{
 document.querySelectorAll('.tabs button').forEach(x=>x.classList.toggle('on',x===b));
 document.querySelectorAll('.tab').forEach(t=>t.classList.toggle('on',t.id===b.dataset.tab))});
let presetKey='';
function renderPresets(){
 const favs=st.log.filter(e=>e.fav).sort((a,b)=>a.freq-b.freq).slice(0,8),key=JSON.stringify(favs.map(e=>[e.freq,e.name]));
 if(key!==presetKey){presetKey=key;$('presets').innerHTML=favs.length?favs.map(e=>'<button data-pf="'+e.freq+'">★ '+esc(e.name)+' <small>'+e.freq.toFixed(1)+'</small></button>').join(''):'<span class="hint" style="margin:0">☆ Star a station in the logbook to pin it here</span>'}
 document.querySelectorAll('#presets button').forEach(b=>b.classList.toggle('on',Math.abs(parseFloat(b.dataset.pf)-freq)<=0.05));
}
$('presets').addEventListener('click',e=>{const b=e.target.closest('button[data-pf]');if(b)setFreq(parseFloat(b.dataset.pf),true)});

buildScale();
show();
loadRec();
loadRegions().then(()=>{
 dirSearch();
 askLocation();
});
function pollLoop(){
 fetch('/api/state').then(r=>r.json()).then(s=>{
  if(!drag)upd(s);
  clearTimeout(pollT);pollT=setTimeout(pollLoop,s.status==='tuning'?250:1000);
 }).catch(()=>{clearTimeout(pollT);pollT=setTimeout(pollLoop,1000)});
}
pollLoop();
</script></body></html>
"""


def prewarm():
    """Probe known stations in the background so the first twist is instant."""
    try:
        build_candidates("http://127.0.0.1/")   # warms mpg123/flatpak detection caches
    except Exception:
        pass
    for e in list(radio.log):
        urls = list(e.get("urls") or [])
        if not urls or e["name"] in _good_url:
            continue
        res = resolve_stream(urls)
        if res:
            _good_url[e["name"]] = res


def main():
    if not shutil.which("curl"):
        sys.exit("[!] curl is required but was not found.")
    try:
        server = ReusableHTTPServer(("127.0.0.1", PORT), Handler)
    except OSError as e:
        sys.exit(f"[!] Could not start the radio server on port {PORT}: {e}")
    url = f"http://127.0.0.1:{PORT}/"
    print(f"📻 Radio running at {url}   (Ctrl+C to switch off)")
    threading.Thread(target=prewarm, daemon=True).start()
    threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nRadio forced offline.")
    finally:
        radio.stop()
        radio.flush()


if __name__ == "__main__":
    main()