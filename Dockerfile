# Use an official lightweight Python image
FROM python:3.11-slim

# Install the system tools your script explicitly requires
RUN apt-get update && apt-get install -y \
    curl \
    mpv \
    mpg123 \
    ffmpeg \
    && rm -rf /var/lib/apt/lists/*

# Set the working directory inside the cloud container
WORKDIR /app

# Copy all your repository files into the container
COPY . /app

# Inform Docker that the application listens on port 8765
EXPOSE 8765

# Run your script when the container starts up
CMD ["python", "PirateRadio.py"]
