import os
from copy import deepcopy
from distutils.dep_util import newer_group

import keyboard
from skimage.metrics import structural_similarity as ssim
from collections import deque

import copy, struct, threading, zlib, time, win32gui, math, win32api, ctypes, win32con, cv2, random, mouse, re, shutil

import __main__

import zhmiscellany

z = zhmiscellany.z
import keyboard as kb
from ctypes import wintypes
# import dill
import pickle as dill  # dill is better in everything but speed, and speed might be needed in this case. If things break then just comment this line out and uncomment dill.
from bisect import insort, bisect
import numpy as np
from PIL import Image
from queue import Queue, Empty
from pydub import AudioSegment
from pydub.playback import play
from skimage.transform import resize
from scipy.cluster.hierarchy import linkage, fcluster
from sklearn.cluster import KMeans

import tempfile, subprocess

is_compiled = not os.path.exists('.git')
if is_compiled and False:
    cfg = __main__.aimbot_object.config_watcher_module.cfg
else:
    from logic.config_watcher import cfg

global time_cooldown, replaying_packets, latest_location, old_xy, macro_listening, latest_location2, latest_location3, macro_intervene
old_xy = [False]
time_cooldown = 0
replaying_packets = False
latest_location = None
latest_location2 = None
latest_location3 = None
macro_listening = cfg.macro_listen
macro_intervene = cfg.enable_macro_intervene


class Capture_Recordings:
    def __init__(self):
        # initilize random variables for later use
        self.p_binary_data_path = r'macro_memory\p_binary_data'
        self.f_binary_data_path = r'macro_memory\f_binary_data'
        self.h_binary_data_path = r'macro_memory\h_binary_data'
        self.b_binary_data_path = r'macro_memory\b_binary_data'
        self.compression_folder = r'macro_memory\compressed'
        self.macro_memory_folder = r'macro_memory'
        self.key_template_data = {
            'press': 'k',
            'signi': 0,
            'flocation': None,
            'location': None,
            'keys_held': None,
            'duration': 0,
            'time': None,
            'window_dimensions': None,
            'window_position': None,
            'area': None,
            'prom_color': None,
        }
        self.mouse_template_data = {
            'press': 'm',
            'signi': 0,
            'mouse_button': None,
            'time': None,
            'window_dimensions': None,
            'window_position': None,
        }
        self.scroll_template_data = {
            'press': 's',
            'signi': 0,
            'flocation': None,
            'location': None,
            'direction': None,
            'time': None,
            'window_dimensions': None,
            'window_position': None,
            'area': None,
            'prom_color': None,
        }
        self.click_args = {1: {}, 2: {'right_click': True}, 3: {'middle_click': True}}
        self.interval = 0.5
        self.actions_per_second = 1 / 32
        self.target_resolution = (64, 36)
        self.recent_frame_p = None
        self.titty = 0
        self.frames, self.packets, self.action_rate = [], [], []
        self.good_packets = []
        self.active_keys = {}
        self.thread_com = {}
        self.action_cooldown = time.time()
        self.intervene_disrupt = 0.0
        self.max_clusters = 5
        self.broke_out_becauseoffreq = 0
        self.broke_out_becauseofmedian = 0
        user32 = ctypes.windll.user32
        self.monitor_x, self.monitor_y = zhmiscellany.misc.get_actual_screen_resolution()
        # self.frame_res = (self.monitor_x, self.monitor_y)
        monitor_center_exact = (self.monitor_x / 2, self.monitor_y / 2)
        settings = win32api.EnumDisplaySettings(None, win32con.ENUM_CURRENT_SETTINGS)
        self.monitor_hertz = settings.DisplayFrequency
        self.hertz_pause = (1 / self.monitor_hertz) * 8
        closest_x = sorted(range(self.monitor_x), key=lambda x: abs(x - monitor_center_exact[0]))[:32]
        closest_y = sorted(range(self.monitor_y), key=lambda y: abs(y - monitor_center_exact[1]))[:32]
        self.monitor_center = {(x, y) for x in closest_x for y in closest_y}
        self.max_distance = round(((self.monitor_x + self.monitor_y) / 200) * 5.5)
        self.file_lock = threading.Lock()
        self.mouse_sound = AudioSegment.from_mp3(r"icons\mouse_replay.mp3")
        self.keyboard_sound = AudioSegment.from_mp3(r"icons\keyboard_replay.mp3")
        self.scroll_sound = AudioSegment.from_mp3(r"icons\scroll_replay.mp3")
        self.listening_on = AudioSegment.from_mp3(r"icons\listening_on.mp3")
        self.listening_off = AudioSegment.from_mp3(r"icons\listening_off.mp3")
        self.intervene_on = AudioSegment.from_mp3(r"icons\intervene_on.mp3")
        self.intervene_off = AudioSegment.from_mp3(r"icons\intervene_off.mp3")
        self.disrupt_sound = AudioSegment.from_mp3(r"icons\disrupt.mp3")

        opftr = 720  # 720p or whatever number is here p
        opftr = (self.monitor_x / (self.monitor_y / opftr), opftr)  # dynamic aspect ratio

        opftr_scale = 0.8  # scale further down by this amount
        opftr = (round(opftr[0] * opftr_scale), round(opftr[1] * opftr_scale))

        self.frame_res = opftr

        self.frame_hashes = {}
        self.recent_frame = []
        self._frames = []

        self.crop_screenshot_size = 80
        self.crop_screenshot_size = round((self.crop_screenshot_size / 1280) * self.frame_res[0])

        class outer_process_code:
            def __init__(self, target_resolution):
                self.target_resolution = target_resolution
                import bettercam, time, cv2
                self.bc = bettercam.create()
                self.previous_frame = None

            def output(self):

                def compress_image(image, quality=50):
                    encode_param = [int(cv2.IMWRITE_JPEG_QUALITY), quality]
                    _, encoded = cv2.imencode(".jpg", image, encode_param)
                    return encoded

                frame = self.bc.grab()
                if frame is None:
                    frame = self.previous_frame
                else:
                    frame = cv2.resize(frame, self.target_resolution, interpolation=cv2.INTER_LANCZOS4)
                    frame = compress_image(frame)
                    self.previous_frame = frame
                return [frame, time.time()]

        os.environ['zhmiscellany_init_ray'] = 'force'
        # start threads
        from zhmiscellany._processing_supportfuncs import _ray_init_thread;
        _ray_init_thread.join()
        self.rawrxd = zhmiscellany.processing.synchronous_class_multiprocess(outer_process_code, opftr)

        # set up glow and controls
        class glow_triple_wrapper:
            def __init__(self):
                import threading
                from PyQt5.QtCore import QTimer

                self.QTimer = QTimer
                self.block_until_ready = False
                threading.Thread(target=self.create).start()

            def is_ready(self):
                return self.block_until_ready

            def create(self):
                import sys
                from PyQt5.QtWidgets import QApplication, QMainWindow, QWidget
                from PyQt5.QtGui import QPainter, QColor
                from PyQt5.QtCore import Qt, QPropertyAnimation, QEasingCurve, pyqtProperty, QTimer, QRect

                import time, threading
                from PyQt5.QtWidgets import QApplication
                from PyQt5.QtCore import QTimer, QObject

                class GlowOverlay(QMainWindow):
                    def __init__(self):
                        super().__init__()
                        self.setWindowTitle("Glow Overlay")

                        # Set up window flags for a frameless, transparent window that stays on top
                        # Add WindowTransparentForInput flag to make the entire window pass-through for mouse events
                        self.setWindowFlags(
                            Qt.FramelessWindowHint |  # DNO
                            Qt.WindowStaysOnTopHint |
                            Qt.Tool |
                            Qt.WindowTransparentForInput  # This is key to make entire window pass clicks through
                        )

                        # Make the window background transparent
                        self.setAttribute(Qt.WA_TranslucentBackground)
                        # This alone isn't enough, but we'll keep it for compatibility
                        self.setAttribute(Qt.WA_TransparentForMouseEvents)

                        # Initialize properties
                        self._opacity = 0.0  # Start fully visible
                        self._color = QColor(0, 255, 0)  # Start with green
                        self._glow_size = 20  # The size of the glow effect in pixels

                        # Color animation properties
                        self._red = 0
                        self._green = 255
                        self._blue = 0

                        # Set up initial window size to cover the entire screen
                        screen_geometry = QApplication.desktop().screenGeometry()
                        self.setGeometry(screen_geometry)

                        # Create central widget
                        self.central_widget = QWidget()
                        self.setCentralWidget(self.central_widget)

                        # Initialize animation object for opacity changes
                        self.fade_animation = QPropertyAnimation(self, b"opacity")
                        self.fade_animation.setEasingCurve(QEasingCurve.InOutQuad)
                        self.fade_animation.setDuration(500)  # Animation duration in ms

                        # Initialize animation objects for color transitions
                        self.red_animation = QPropertyAnimation(self, b"red")
                        self.red_animation.setEasingCurve(QEasingCurve.InOutQuad)
                        self.red_animation.setDuration(500)  # Animation duration in ms

                        self.green_animation = QPropertyAnimation(self, b"green")
                        self.green_animation.setEasingCurve(QEasingCurve.InOutQuad)
                        self.green_animation.setDuration(500)  # Animation duration in ms

                        self.blue_animation = QPropertyAnimation(self, b"blue")
                        self.blue_animation.setEasingCurve(QEasingCurve.InOutQuad)
                        self.blue_animation.setDuration(500)  # Animation duration in ms

                        # Show the window
                        self.show()

                    def paintEvent(self, event):
                        """Custom paint event to draw the glow effect"""
                        painter = QPainter(self)
                        painter.setRenderHint(QPainter.Antialiasing)

                        width = self.width()
                        height = self.height()
                        glow_size = self._glow_size

                        # Create a color with the current opacity
                        glow_color = QColor(self._red, self._green, self._blue)

                        # Draw the glow effect on all four edges
                        # Top edge
                        for i in range(glow_size):
                            alpha = 255 * (1 - i / glow_size) * self._opacity
                            glow_color.setAlpha(int(alpha))
                            painter.setPen(glow_color)
                            painter.drawLine(0, i, width, i)

                        # Bottom edge
                        for i in range(glow_size):
                            alpha = 255 * (1 - i / glow_size) * self._opacity
                            glow_color.setAlpha(int(alpha))
                            painter.setPen(glow_color)
                            painter.drawLine(0, height - i - 1, width, height - i - 1)

                        # Left edge
                        for i in range(glow_size):
                            alpha = 255 * (1 - i / glow_size) * self._opacity
                            glow_color.setAlpha(int(alpha))
                            painter.setPen(glow_color)
                            painter.drawLine(i, 0, i, height)

                        # Right edge
                        for i in range(glow_size):
                            alpha = 255 * (1 - i / glow_size) * self._opacity
                            glow_color.setAlpha(int(alpha))
                            painter.setPen(glow_color)
                            painter.drawLine(width - i - 1, 0, width - i - 1, height)

                    # Override these methods to ensure the window never takes focus or captures clicks
                    def mousePressEvent(self, event):
                        event.ignore()

                    def mouseReleaseEvent(self, event):
                        event.ignore()

                    def mouseMoveEvent(self, event):
                        event.ignore()

                    # Define properties for animation
                    def get_opacity(self):
                        return self._opacity

                    def set_opacity(self, opacity):
                        self._opacity = opacity
                        self.update()  # Trigger repaint

                    def get_red(self):
                        return self._red

                    def set_red(self, red):
                        self._red = red
                        self._color = QColor(self._red, self._green, self._blue)
                        self.update()  # Trigger repaint

                    def get_green(self):
                        return self._green

                    def set_green(self, green):
                        self._green = green
                        self._color = QColor(self._red, self._green, self._blue)
                        self.update()  # Trigger repaint

                    def get_blue(self):
                        return self._blue

                    def set_blue(self, blue):
                        self._blue = blue
                        self._color = QColor(self._red, self._green, self._blue)
                        self.update()  # Trigger repaint

                    # Create pyqtProperties for use with QPropertyAnimation
                    opacity = pyqtProperty(float, get_opacity, set_opacity)
                    red = pyqtProperty(int, get_red, set_red)
                    green = pyqtProperty(int, get_green, set_green)
                    blue = pyqtProperty(int, get_blue, set_blue)

                    # Methods to control the glow
                    def set_color(self, color_name):
                        """Change the glow color to either 'green' or 'red'"""
                        if color_name.lower() == "green":
                            self._animate_color(0, 255, 0)
                        elif color_name.lower() == "red":
                            self._animate_color(255, 0, 0)
                        self.update()

                    def _animate_color(self, r, g, b):
                        """Animate color transition to the specified RGB values"""
                        # Stop any running animations
                        self.red_animation.stop()
                        self.green_animation.stop()
                        self.blue_animation.stop()

                        # Setup animations for each color component
                        self.red_animation.setStartValue(self._red)
                        self.red_animation.setEndValue(r)

                        self.green_animation.setStartValue(self._green)
                        self.green_animation.setEndValue(g)

                        self.blue_animation.setStartValue(self._blue)
                        self.blue_animation.setEndValue(b)

                        # Start the animations
                        self.red_animation.start()
                        self.green_animation.start()
                        self.blue_animation.start()

                    def fade_in(self):
                        """Fade the glow in quickly (200ms) then fade to a lower opacity (0.5) once fade_in is done."""
                        if self.fade_animation.state() == QPropertyAnimation.Running:
                            self.fade_animation.stop()

                        # Disconnect any previous finished signal connections to avoid duplicate calls.
                        try:
                            self.fade_animation.finished.disconnect()
                        except Exception:
                            pass

                        # Connect the finished signal to call vibe_out with a specified duration.

                        # Set up fade-in animation (200ms to full opacity)
                        self.fade_animation.setDuration(200)
                        self.fade_animation.setStartValue(self._opacity)
                        self.fade_animation.setEndValue(1.0)
                        self.fade_animation.start()

                    def fade_out(self):
                        """Fade the glow out quickly, overriding any currently running animations."""
                        # Stop any running animations
                        if self.fade_animation.state() == QPropertyAnimation.Running:
                            self.fade_animation.stop()
                        if self.red_animation.state() == QPropertyAnimation.Running:
                            self.red_animation.stop()
                        if self.green_animation.state() == QPropertyAnimation.Running:
                            self.green_animation.stop()

                        # Optionally disconnect any finish signal connections to avoid triggering callbacks from other animations
                        try:
                            self.fade_animation.finished.disconnect()
                        except Exception:
                            pass

                        # Set up the quick fade-out animation (200ms to 0 opacity)
                        self.fade_animation.setDuration(200)
                        self.fade_animation.setStartValue(self._opacity)
                        self.fade_animation.setEndValue(0.0)
                        self.fade_animation.start()

                    def vibe_out(self, duration=3000):
                        """If the current color is green, slowly fade the glow to 0.5 opacity over a given duration."""
                        # Check if the current color is exactly green (0, 255, 0)
                        if self.fade_animation.state() == QPropertyAnimation.Running:
                            self.fade_animation.stop()

                        # Set the animation duration based on the provided variable
                        self.fade_animation.setDuration(duration)
                        self.fade_animation.setStartValue(self._opacity)
                        self.fade_animation.setEndValue(0.3)
                        self.fade_animation.start()

                    def toggle_color(self):
                        """Toggle between green and red with a smooth transition"""
                        if self._green > self._red:  # If currently green
                            self.set_color("red")
                        else:  # If currently red
                            self.set_color("green")

                    def set_to_green(self):
                        """Toggle between green and red with a smooth transition"""
                        if self._green > self._red:  # If currently green
                            pass
                        else:  # If currently red
                            self.set_color("green")

                    def set_to_red(self):
                        """Toggle between green and red with a smooth transition"""
                        if self._green > self._red:  # If currently green
                            self.set_color("red")
                        else:  # If currently red
                            pass

                from PyQt5.QtWidgets import QApplication
                app = QApplication([])
                self.overlay = GlowOverlay()
                self.block_until_ready = True
                app.exec_()

            def set_color(self, color):
                self.QTimer.singleShot(0, lambda c=color: self.overlay.set_color(c))  # schedule in main thread

            def fade_in(self):
                self.QTimer.singleShot(0, self.overlay.fade_in)

            def fade_out(self):
                self.QTimer.singleShot(0, self.overlay.fade_out)

            def toggle_color(self):
                self.QTimer.singleShot(0, self.overlay.toggle_color)

            def vibe_out(self):
                self.QTimer.singleShot(0, self.overlay.vibe_out)

            def set_green(self):
                self.QTimer.singleShot(0, self.overlay.set_to_green)

            def set_red(self):
                self.QTimer.singleShot(0, self.overlay.set_to_red)

            def stop(self):
                self.QTimer.singleShot(0, self.overlay.close)

        self.glow_control = zhmiscellany.processing.synchronous_class_multiprocess(glow_triple_wrapper)
        while not self.glow_control.is_ready():
            time.sleep(0.05)

        def read_saved_packets_with_recovery(file):
            while True:
                size_data = file.read(4)
                if not size_data:
                    break
                try:
                    chunk_size = struct.unpack('<I', size_data)[0]
                    if chunk_size > 1_000_000:  # Sanity check for chunk size
                        file.seek(-1, 1)
                        continue
                    chunk = file.read(chunk_size)
                    if len(chunk) != chunk_size:
                        break
                    yield chunk
                except struct.error:
                    break

        def read_saved_packets_with_recovery_bytes(data):
            i, n = 0, len(data)
            while i < n:
                if i + 4 > n:
                    break
                size_data = data[i: i + 4]
                i += 4
                try:
                    chunk_size = struct.unpack('<I', size_data)[0]
                    if chunk_size > 1_000_000:  # Sanity check for chunk size
                        i -= 1
                        continue
                    if i + chunk_size > n:
                        break
                    yield data[i: i + chunk_size]
                    i += chunk_size
                except struct.error:
                    break

        def load_all():
            saved_packets = []
            saved_frames = []
            saved_hash = {}
            saved_bad_packets = set()
            bad, total = 0, 0

            # Load data from compressed files
            if os.path.exists(self.compression_folder):
                files = [os.path.join(self.compression_folder, f) for f in os.listdir(self.compression_folder)]
                files.sort(key=lambda p: int(re.search(r'^(\d+)', os.path.basename(p)).group(1)))

                for path in files:
                    filename = os.path.basename(path)
                    try:
                        data = zlib.decompress(open(path, 'rb').read())
                        total_before = total

                        if '_p_compressed' in filename:
                            target = saved_packets
                        elif '_f_compressed' in filename:
                            target = saved_frames
                        elif '_h_compressed' in filename:
                            for chunk in read_saved_packets_with_recovery_bytes(data):
                                total += 1
                                try:
                                    saved_hash.update(dill.loads(chunk))
                                except Exception:
                                    bad += 1
                            continue
                        elif '_b_compressed' in filename:
                            for chunk in read_saved_packets_with_recovery_bytes(data):
                                total += 1
                                try:
                                    saved_bad_packets.add(dill.loads(chunk))
                                except Exception:
                                    bad += 1
                            continue
                        else:
                            continue

                        # Process chunks for packets and frames (append operation)
                        for chunk in read_saved_packets_with_recovery_bytes(data):
                            total += 1
                            try:
                                target.append(dill.loads(chunk))
                            except Exception:
                                bad += 1

                    except Exception as e:
                        print(f"Error processing compressed file {filename}: {e}")

            # Load data from regular binary files
            binary_paths = [
                (self.p_binary_data_path, saved_packets, False),
                (self.f_binary_data_path, saved_frames, False),
                (self.h_binary_data_path, saved_hash, True),
                (self.b_binary_data_path, saved_bad_packets, None),
            ]

            for file_path, target, is_hash in binary_paths:
                if os.path.exists(file_path):
                    try:
                        with open(file_path, 'rb') as f:
                            for chunk in read_saved_packets_with_recovery(f):
                                total += 1
                                try:
                                    data = dill.loads(chunk)
                                    if is_hash is True:
                                        target.update(data)
                                    elif is_hash is None:
                                        target.add(data)
                                    else:
                                        target.append(data)
                                except Exception:
                                    bad += 1
                    except Exception as e:
                        print(f"Error processing binary file {file_path}: {e}")

            return saved_packets, saved_frames, saved_hash, saved_bad_packets, total, bad

        # usage
        self.packets, self.frames, self.frame_hashes, self.bad_packets, processed, errors = load_all()
        self.frames.sort(key=lambda x: x['signi'], reverse=True)
        self.capture_screenshot(True)  # make sure shit ain't empty ait?
        time.sleep(0.1)
        threading.Thread(target=self.compressor).start()
        threading.Thread(target=self.mouse_collector).start()
        threading.Thread(target=self.toggle_intervene).start()
        threading.Thread(target=self.key_collector).start()
        threading.Thread(target=self.screenshot_loop).start()
        threading.Thread(target=self.screen_intervene).start()
        threading.Thread(target=self.activity_ratio).start()
        threading.Thread(target=self.check_visual).start()
        print('capture_cursor loaded')

    def check_visual(self):
        reload = cfg.show_outer_glow
        while True:
            if not cfg.show_outer_glow or not cfg.enable_super_macro:
                self.glow_control.fade_out()
                reload = True
            else:
                if macro_listening and reload:
                    reload = False
                    self.glow_control.fade_in()
                    time.sleep(0.2)
                    if macro_listening: self.glow_control.vibe_out()
            time.sleep(0.5)

    def turn_on(self):
        global macro_listening
        if cfg.show_outer_glow:
            self.glow_control.set_green()
            self.glow_control.fade_in()
            time.sleep(0.2)
            if macro_listening: self.glow_control.vibe_out()

    def intervene_glow(self):
        if cfg.show_outer_glow:
            self.glow_control.set_red()
            self.glow_control.fade_in()

    def back_to_listen(self):
        if cfg.show_outer_glow:
            self.glow_control.set_green()
            self.glow_control.vibe_out()

    def turn_off(self):
        global macro_listening, replaying_packets
        if not replaying_packets:
            self.glow_control.fade_out()

    from PyQt5.QtCore import QTimer

    def toggle_intervene(self):
        def on_key_event(event):
            global macro_listening, macro_intervene
            # Only process key down events.
            if not cfg.enable_super_macro: return
            if event.event_type != "down":
                return

            # Split the current hotkey string on commas and strip extra whitespace.
            l_hotkey_strings = [hk.strip() for hk in cfg.hotkey_macro_listen.split(',')]

            # Convert each key string to its scan codes and flatten the result.
            l_keycodes = []
            for key in l_hotkey_strings:
                codes = keyboard.key_to_scan_codes(key)
                if codes:
                    l_keycodes.extend(codes)

            # If no valid keycodes were found, do nothing.
            if not l_keycodes:
                return
            i_hotkey_strings = [hk.strip() for hk in cfg.hotkey_macro_intervene.split(',')]

            # Convert each key string to its scan codes and flatten the result.
            i_keycodes = []
            for key in i_hotkey_strings:
                codes = keyboard.key_to_scan_codes(key)
                if codes:
                    i_keycodes.extend(codes)

            # If no valid keycodes were found, do nothing.
            if not i_keycodes:
                return
            # Toggle macro_listening if the event's scan code matches one of the keycodes.
            if event.scan_code in l_keycodes and self.toggle_cooldown <= time.time():
                macro_listening = not macro_listening
                self.toggle_cooldown = time.time() + 0.05
                print("Listening toggled to:", macro_listening)

                # Update config value
                cfg.macro_listen = macro_listening

                # Visual effects - call directly, not as a thread target
                if macro_listening:
                    self.play_audio(self.listening_on)
                    self.turn_on()
                else:
                    self.play_audio(self.listening_off)
                    self.turn_off()

                # Update GUI widget if possible
                try:
                    if hasattr(__main__, 'settings_gui') and hasattr(__main__.settings_gui, 'widgets'):
                        # Check if 'Super Macro' section exists
                        if 'Super Macro' in __main__.settings_gui.widgets:
                            if 'macro_listen' in __main__.settings_gui.widgets['Super Macro']:
                                widget = __main__.settings_gui.widgets['Super Macro']['macro_listen']

                                # Handle different widget types
                                if hasattr(widget, 'setChecked'):
                                    # Direct CustomSwitch or QCheckBox
                                    widget.setChecked(macro_listening)
                                elif hasattr(widget, 'checkbox'):
                                    # CustomSwitch where checked state is in a child checkbox
                                    widget.checkbox.setChecked(macro_listening)

                                # Update the config in the GUI
                                if hasattr(__main__.settings_gui.config, 'set'):
                                    __main__.settings_gui.config.set('Super Macro', 'macro_listen', str(macro_listening).lower())

                                # Force GUI update
                                # if hasattr(__main__.settings_gui, 'repaint'):
                                #     __main__.settings_gui.repaint()

                                # Process any pending events to ensure the GUI updates
                                # if hasattr(__main__, 'QApplication') and hasattr(__main__.QApplication, 'processEvents'):
                                #     __main__.QApplication.processEvents()
                except Exception as e:
                    print(f"Error updating GUI: {str(e)}")

            if event.scan_code in i_keycodes and self.toggle_cooldown <= time.time():
                macro_intervene = not macro_intervene
                self.toggle_cooldown = time.time() + 0.05
                if macro_intervene:
                    self.play_audio(self.intervene_on)
                else:
                    if macro_listening:
                        self.back_to_listen()
                    else:
                        self.turn_off()
                    self.play_audio(self.intervene_off)
                print("intervene set to :", macro_intervene)

                # Update config value
                cfg.enable_macro_intervene = macro_intervene

                # Update GUI widget if possible
                try:
                    if hasattr(__main__, 'settings_gui') and hasattr(__main__.settings_gui, 'widgets'):
                        # Check if 'Super Macro' section exists
                        if 'Super Macro' in __main__.settings_gui.widgets:
                            if 'enable_macro_intervene' in __main__.settings_gui.widgets['Super Macro']:
                                widget = __main__.settings_gui.widgets['Super Macro']['enable_macro_intervene']

                                # Handle different widget types
                                if hasattr(widget, 'setChecked'):
                                    # Direct CustomSwitch or QCheckBox
                                    widget.setChecked(macro_intervene)
                                elif hasattr(widget, 'checkbox'):
                                    # CustomSwitch where checked state is in a child checkbox
                                    widget.checkbox.setChecked(macro_intervene)

                                # Update the config in the GUI
                                if hasattr(__main__.settings_gui.config, 'set'):
                                    __main__.settings_gui.config.set('Super Macro', 'enable_macro_intervene', str(macro_intervene).lower())

                                # Force GUI update
                                # if hasattr(__main__.settings_gui, 'repaint'):
                                #     __main__.settings_gui.repaint()

                                # Process any pending events to ensure the GUI updates
                                if hasattr(__main__, 'QApplication') and hasattr(__main__.QApplication, 'processEvents'):
                                    __main__.QApplication.processEvents()
                except Exception as e:
                    print(f"Error updating GUI: {str(e)}")

        self.toggle_cooldown = time.time()
        keyboard.hook(on_key_event)

        # Block the thread if needed to keep the listener active.
        keyboard.wait()

    def play_audio(self, file_sound, range=(1.2, 1.3)):
        sound = file_sound
        sound = sound._spawn(sound.raw_data, overrides={'frame_rate': int(sound.frame_rate * random.uniform(*range))})

        def safe_play(audio_segment):  # pydub is ass - zh
            with tempfile.NamedTemporaryFile(delete=False, suffix=".wav") as f:
                temp_path = f.name
            audio_segment.export(temp_path, format="wav")
            subprocess.call(["ffplay", "-nodisp", "-autoexit", temp_path])
            os.remove(temp_path)

        zhmiscellany.processing.multiprocess_threaded(safe_play, (sound,))

    def screenshot_loop(self):
        """a loop that constantally saves screenshots for use"""
        global replaying_packets, macro_listening
        # starts screenshot loop, so every so often an array filled with rgb values can be acted upon later
        next_capture_time = time.time()
        while True:
            if cfg.enable_super_macro and not replaying_packets and (macro_listening or macro_intervene):
                self.capture_screenshot()
                next_capture_time += cfg.intervene_rate
            else:
                time.sleep(cfg.intervene_rate)

    def wait_for_vsync(self):
        ctypes.windll.dwmapi.DwmFlush()

    def add_contrast(self, img, factor=1.2):  # factor ~20% increase
        return cv2.convertScaleAbs(img, alpha=factor, beta=0)

    def increase_saturation(self, img, factor=1.2):  # factor ~20% increase
        hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
        hsv[..., 1] = np.clip(hsv[..., 1].astype(np.float32) * factor, 0, 255).astype(np.uint8)
        return cv2.cvtColor(hsv, cv2.COLOR_HSV2BGR)

    def get_screen_pixels(self, wait=False, contrast=1.2, saturation=1.4):
        if wait:
            self.wait_for_vsync()
        soup = self.rawrxd.output()
        frame = cv2.imdecode(soup[0], cv2.IMREAD_COLOR)
        frame_lag = time.time() - soup[1]
        if frame_lag > 0.1:
            z.l('WARNING FRAME LAG DETECTED', frame_lag)
        frame = self.add_contrast(frame, contrast)
        frame = self.increase_saturation(frame, saturation)
        return frame

    def capture_screenshot(self, bypass=False):
        global old_xy
        # creates the rgb array of the screen and stores it into memory. for efficiency, a hash system was used
        # if not bypass and self.action_rate:
        #     signi = sum(self.action_rate) / len(self.action_rate)
        # else:
        #     signi = 0.01
        # if signi > 0.0 or bypass:
        if not bypass and self.action_rate:
            signi = sum(self.action_rate) / len(self.action_rate)
        else:
            signi = 0.0
        frame = None
        while frame is None:
            try:
                screen = self.get_screen_pixels()
            except Exception as e:
                print(f'Error getting screenshot: {e}')
                screen = None
            try:
                frame = screen
            except:
                print(f'screen was unable to be turned into a frame, trying again tho. screen: {screen}')
        small_frame = cv2.resize(frame, self.target_resolution, interpolation=cv2.INTER_LANCZOS4)
        current_hash = f'{zhmiscellany.misc.md5_int_hash(small_frame)}'
        packet = {'signi': signi, 'hash': current_hash, 'time': time.time()}

        self.recent_frame_p = small_frame
        if (not any(old_xy) or bypass) and macro_listening and signi > 0.0:
            if current_hash not in self.frame_hashes:
                self.frame_hashes[current_hash] = small_frame
                with open(self.h_binary_data_path, 'ab') as file:
                    self.write_chunk(file, dill.dumps({current_hash: small_frame}, protocol=5))
            insort(self.frames, packet, key=lambda x: x["signi"])
            with open(self.f_binary_data_path, 'ab') as file:
                self.write_chunk(file, dill.dumps(packet, protocol=5))
        self.recent_frame.append((frame, time.time()))
        if self.recent_frame[0][1] < time.time() - 1:
            self.recent_frame.pop(0)

    def activity_ratio(self):
        """tries assuming just how active the user is by comparing all recent packets 'signi' value. This is helpful for getting relavent screenshots quicker"""
        while True:
            new_values = []
            for value in self.action_rate:
                decayed = value * (1 - 0.1)
                if decayed > 0.01:
                    new_values.append(decayed)
            self.action_rate = new_values
            time.sleep(0.5)

    def get_focused_window_info(self):
        hwnd = win32gui.GetForegroundWindow()
        if not hwnd: return None, None
        rect = win32gui.GetWindowRect(hwnd)
        position = (rect[0], rect[1])
        size = (rect[2] - rect[0], rect[3] - rect[1])
        return position, size

    def area_signi(self, target_color: tuple, threshold: int = 10) -> float:
        similar_score = 0.0
        total_count = 0
        ct = time.time() + 0.1
        for packet in self.packets:
            if time.time() > ct: break
            avg_area = packet.get('prom_color')
            if avg_area is not None:
                total_count += 1
                # Cast each component to int before subtraction to avoid overflow
                diff = sum(abs(int(c1) - int(c2)) for c1, c2 in zip(avg_area, target_color))
                max_diff = threshold * 3  # Since RGB has 3 channels
                similarity_weight = max(0, 1 - (diff / max_diff))  # Normalize between 0 and 1
                similar_score += similarity_weight
        return similar_score / total_count if total_count else 0.0

    def compute_histogram(self, image, histSize=(16, 16, 16)):
        image = cv2.cvtColor(image, cv2.COLOR_RGB2BGR)
        hist = cv2.calcHist([image], [0, 1, 2], None, histSize, [0, 256, 0, 256, 0, 256])
        cv2.normalize(hist, hist)
        return hist.flatten()

    def compute_color_ssim(self, imageA, imageB):
        min_dim = min(imageA.shape[:2])  # Get smallest spatial dimension
        win_size = max(3, min(7, min_dim if min_dim % 2 == 1 else min_dim - 1))  # Ensure odd and >= 3
        score, _ = ssim(imageA, imageB, channel_axis=-1, win_size=win_size, full=True)
        return score

    def normalize_array(self, array: np.ndarray) -> np.ndarray:
        # Normalize array to standard format for comparison.

        # Args:
        #     array: Input numpy array (can be any shape)

        # Returns:
        #     Normalized array with shape (N,) where N is a fixed size

        # Ensure array is at least 2D
        if array.ndim == 1:
            array = np.expand_dims(array, axis=0)

        # Resize to fixed dimensions if needed
        target_height, target_width = 64, 64  # Standard size
        if array.shape[0] != target_height or array.shape[1] != target_width:
            try:
                # Try to resize if it's an image
                if array.ndim >= 2:
                    array = cv2.resize(array, (target_width, target_height),
                                       interpolation=cv2.INTER_AREA)
            except Exception:
                # If resize fails, pad or crop
                if array.ndim >= 2:
                    # Get current dimensions
                    h, w = array.shape[:2]

                    # Create target array
                    target_shape = (target_height, target_width)
                    if array.ndim > 2:
                        target_shape += (array.shape[2],)

                    result = np.zeros(target_shape, dtype=array.dtype)

                    # Copy as much as will fit
                    h_to_copy = min(h, target_height)
                    w_to_copy = min(w, target_width)
                    result[:h_to_copy, :w_to_copy] = array[:h_to_copy, :w_to_copy]
                    array = result

        return array

    def extract_features(self, area: np.ndarray) -> np.ndarray:
        # Extract robust features from an image area.
        # Works with arrays of any dimension.

        # Args:
        #     area: Image area (numpy array)

        # Returns:
        #     Feature vector

        # Normalize array dimensions
        normalized = self.normalize_array(area)

        # Extract color histogram features
        if normalized.ndim == 3 and normalized.shape[2] == 3:  # RGB
            # Pre-allocate histogram arrays for better performance
            hist_r = np.histogram(normalized[:, :, 0], bins=8, range=(0, 256))[0]
            hist_g = np.histogram(normalized[:, :, 1], bins=8, range=(0, 256))[0]
            hist_b = np.histogram(normalized[:, :, 2], bins=8, range=(0, 256))[0]
            hist_features = np.concatenate([hist_r, hist_g, hist_b])
        else:
            hist_features = np.histogram(normalized, bins=24, range=(0, 256))[0]

        # Add basic statistics - compute once and reuse
        if normalized.ndim == 3:
            # Compute along spatial dimensions only
            mean_val = normalized.mean(axis=(0, 1))
            m2 = np.mean(normalized ** 2, axis=(0, 1))
            variance = np.maximum(m2 - mean_val ** 2, 0)  # Avoid negative values
            std_val = np.sqrt(variance)
            stats = np.concatenate([mean_val, std_val])
        else:
            # For grayscale or other formats
            stats = np.array([np.mean(normalized), np.std(normalized)])

        # Concatenate features
        return np.concatenate([hist_features, stats])

    def cluster_items(self, items, areas):
        n_items = len(items)
        if n_items == 0:
            return []

        # If there are fewer items than max_clusters, each item is its own cluster.
        if n_items <= self.max_clusters:
            return [[i] for i in range(n_items)]

        # Vectorized feature extraction.
        features = np.array([self.extract_features(area) for area in areas])
        features = np.nan_to_num(features)

        n_clusters = min(self.max_clusters, n_items)
        clusterer = KMeans(n_clusters=n_clusters, random_state=0, n_init=1)
        labels = clusterer.fit_predict(features)

        # Group indices by label using numpy's fast sorting and splitting.
        order = np.argsort(labels)
        _, idx = np.unique(labels[order], return_index=True)
        clusters = [list(c) for c in np.split(order, idx[1:])]
        return clusters

    def merge_unique_items(self, items, threshold):
        # Build an array of avg_area values.
        colors = []
        valid_indices = []
        for i, item in enumerate(items):
            # Expect avg_area to be present.
            if 'prom_color' in item:
                colors.append(item['prom_color'])
                valid_indices.append(i)
            else:
                colors.append([0, 0, 0])
                valid_indices.append(i)
        colors = np.array(colors, dtype=np.float32)

        # If there's only one item, nothing to merge.
        if len(colors) < 2:
            return items

        # Perform hierarchical clustering.
        Z = linkage(colors, method='average')
        clusters = fcluster(Z, t=threshold, criterion='distance')

        # Group items by cluster id.
        merged = {}
        for idx, cid in enumerate(clusters):
            merged.setdefault(cid, []).append(items[idx])

        merged_items = []
        for group in merged.values():
            # Only merge if there is more than one item;
            # if the group is a singleton, keep it as is.
            if len(group) == 1:
                merged_items.append(group[0])
            else:
                # Merge the group: choose the one with the highest weight.
                rep = max(group, key=lambda x: x.get('weight', 0))
                # Combine alternate areas from the group (unique numpy arrays).
                unique_alternate = []
                seen_keys = set()
                for item in group:
                    for a in item.get('alternate_areas', []):
                        # Ensure a is a numpy array.
                        arr = np.array(a)
                        # Create a hashable key for uniqueness check.
                        key = arr.tobytes()
                        if key not in seen_keys:
                            unique_alternate.append(arr)
                            seen_keys.add(key)
                rep['alternate_areas'] = unique_alternate
                merged_items.append(rep)
        return merged_items

    def remove_similar_areas(self, flat, hist):
        """because all memories are converged, there will be plenty of duplicated events. this helps remove them all and leaves unique items"""
        # Build combined list from flat/hist.
        combined_items = [{'dict': d, 'origin': 'flat', 'hist': h} for d, h in zip(flat, hist)]
        if not combined_items:
            return []

        # Extract areas from dictionaries.
        all_areas = [item['dict']['area'] for item in combined_items]

        # Cluster similar areas based on their 'area' values.
        area_clusters = self.cluster_items(combined_items, all_areas)

        unique_items = []
        total = len(combined_items)
        # Initial threshold for grouping by prom_color (Euclidean distance in RGB space)
        color_diff_threshold = 20

        # Process each cluster.
        for cluster in area_clusters:
            if not cluster:
                continue

            group = [combined_items[i] for i in cluster]

            # Further group by 'prom_color' (the prominent non-gray color)
            subclusters = []
            for item in group:
                avg_color = np.array(item['dict'].get('prom_color', [0, 0, 0]))
                assigned = False
                for sub in subclusters:
                    rep_color = np.array(sub[0]['dict'].get('prom_color', [0, 0, 0]))
                    if np.linalg.norm(avg_color - rep_color) < color_diff_threshold:
                        sub.append(item)
                        assigned = True
                        break
                if not assigned:
                    subclusters.append([item])

            # For each subcluster, select a representative and record alternate areas.
            for sub in subclusters:
                # First try to pick one that carries 'repeat' in its dict.
                preferred = [item for item in sub if 'repeat' in item['dict']]
                if preferred:
                    rep = max(preferred, key=lambda x: x.get('weight', 0))
                else:
                    # Fallback: prefer items with origin 'flat'
                    flat_sub = [item for item in sub if item['origin'] == 'flat']
                    rep = max(flat_sub, key=lambda x: x.get('weight', 0)) if flat_sub else max(sub, key=lambda x: x.get('weight', 0))

                # Create (or extend) the alternate_areas list using all 'flat' items from subcluster.
                alt_areas = [item['dict']['area'] for item in sub if item['origin'] == 'flat']
                rep['dict']['alternate_areas'] = rep['dict'].get('alternate_areas', []) + alt_areas
                rep['dict']['weight'] = len(sub) / total
                unique_items.append(rep['dict'])

        # Adaptive merging of unique_items based on prom_color.
        # Define a merge function that uses hierarchical clustering over the prom_color values

        merging_threshold = color_diff_threshold
        merged_unique = unique_items
        # Increase merging threshold gradually until unique items are at or below max_clusters.
        while len(merged_unique) > self.max_clusters:
            merged_unique = self.merge_unique_items(merged_unique, merging_threshold)
            merging_threshold *= 1.5
            # Break to avoid an infinite loop.
            if merging_threshold > 255:
                break

        merged_unique.sort(key=lambda x: x.get('weight', 0), reverse=True)
        return merged_unique

    def are_rgbs_similar(self, rgb1, rgb2, return_bool=True, thresh=0.85):
        # ensure inputs are arrays
        a, b = np.array(rgb1, dtype=float), np.array(rgb2, dtype=float)
        score = max(0, 1 - np.linalg.norm(a - b) / 30)
        return score > thresh if return_bool else score

    def are_arrays_similar(self, areas=None, first_array=None, second_array=None, histSize=(16, 16, 16), hist=False, hist_similarity_threshold=0.5, histograms=None):
        # Setup areas list from parameters if not directly provided.
        if histograms is None:
            if areas is None:
                areas = [first_array, second_array]
            if len(areas) < 2:
                if hist:
                    return [], 0, None
                return False
            # Compute histograms for all areas.
            histograms = [self.compute_histogram(area, histSize) for area in areas]
        # Iterate over adjacent pairs of histograms.
        strikes = 0
        for i in range(len(histograms) - 1):
            # Compare histograms using correlation (1.0 indicates identical).
            corr = cv2.compareHist(histograms[i], histograms[i + 1], cv2.HISTCMP_CORREL)
            if corr < hist_similarity_threshold:
                strikes += 1
        # All histograms are considered similar only if no dissimilar pair is found.
        similar = (strikes == 0)
        # Return based on the `hist` flag.
        if hist:
            return similar, histograms
        return similar

    def get_recent_frame(self, offset=None, minimum=None, maximum=None):
        if offset:
            current_time = time.time()
            target = current_time + offset
            valid_frames = [
                frame for frame in self.recent_frame
                if (minimum is None or frame[1] <= current_time + minimum) and (maximum is None or frame[1] >= current_time + maximum)]
            if not valid_frames:
                raise ValueError("No available frame within the specified minimum and maximum range.")
            recent_frame = min(valid_frames, key=lambda x: abs(x[1] - target))
        else:
            return self.recent_frame[-1]
        return recent_frame

    def scale_inwards(self, x, y):  # scale xy from monitor space to 720p screenshot space
        x = round((x / self.monitor_x) * self.frame_res[0])
        y = round((y / self.monitor_y) * self.frame_res[1])
        return x, y

    def scale_outwards(self, x, y):  # scale xy from 720p screenshot space to monitor space
        x = round((x / self.frame_res[0]) * self.monitor_x)
        y = round((y / self.frame_res[1]) * self.monitor_y)
        return x, y

    def average_rgb(self, image):
        return tuple(image.mean(axis=(0, 1)).astype(int))

    def area_screenshot(self, x, y):
        """rewinds time to get the best ss"""
        viewed_ss = self.get_recent_frame(-0.1)[0]
        latest_ss = self.crop_screenshot(x, y, viewed_ss)
        for ss in np.arange(-0.25, -0.5, -0.05):
            arr = self.get_recent_frame(ss)[0]
            if np.array_equal(arr, viewed_ss): continue
            viewed_ss = arr
            new_array = self.crop_screenshot(x, y, arr)
            if self.are_arrays_similar(latest_ss, new_array, (abs(ss) ** abs(ss)) * 0.4) and self.are_rgbs_similar(self.average_rgb(latest_ss), self.average_rgb(new_array)):
                latest_ss = new_array
            else:
                break
        return latest_ss

    def crop_screenshot(self, x, y, recent_frame):
        # tries diligently cropping the x, y to a very nearby point to where the actual click occured, so more useful screenshots are captured (this is good because it's rare people actually click
        # in the center of every button they press)
        base_threshold = 0.05  # Stricter near center
        threshold_growth = 0.02  # Loosens as it expands

        x, y = self.scale_inwards(x, y)
        if recent_frame is None:
            return None

        # Adjust x, y
        x, y = self.move_to_interesting(recent_frame, x, y)

        H_img, W_img = recent_frame.shape[:2]
        s = self.crop_screenshot_size
        xs, ys = max(0, x - s // 2), max(0, y - s // 2)
        xe, ye = min(W_img, x + s // 2), min(H_img, y + s // 2)
        region = recent_frame[ys:ye, xs:xe].copy()
        region_f = region.astype(np.float32)
        H, W, _ = region.shape
        cy, cx = H // 2, W // 2

        # Expand outward with adaptive threshold
        new_left = self.expand_edge(region_f[cy, :], cx, -1, base_threshold, threshold_growth)
        new_right = self.expand_edge(region_f[cy, :], cx, 1, base_threshold, threshold_growth)
        new_top = self.expand_edge(region_f[:, cx], cy, -1, base_threshold, threshold_growth)
        new_bottom = self.expand_edge(region_f[:, cx], cy, 1, base_threshold, threshold_growth)

        if new_left >= new_right or new_top >= new_bottom:
            cropped = region
        else:
            cropped = region[new_top:new_bottom + 1, new_left:new_right + 1]

        # Try to detect a square frame inside the cropped region.
        frame_bbox = self.detect_square_frame(cropped)
        if frame_bbox is not None:
            fx, fy, fw, fh = frame_bbox
            cropped = cropped[fy:fy + fh, fx:fx + fw]
        return cropped

    def expand_edge(self, line, center, direction, base_threshold, threshold_growth, margin=15):
        avg = line[center].copy()
        count = 1
        idx = center
        n = len(line)

        while 0 <= idx + direction < n:
            next_idx = idx + direction
            dist_from_center = abs(next_idx - center)

            # Always keep at least 'margin' pixels from center
            if dist_from_center < margin:
                avg = (avg * count + line[next_idx]) / (count + 1)
                count += 1
                idx = next_idx
                continue

            # Adaptive threshold: stricter near center, looser as it expands
            threshold = base_threshold + dist_from_center * threshold_growth
            if np.linalg.norm(line[next_idx] - avg) < threshold:
                avg = (avg * count + line[next_idx]) / (count + 1)
                count += 1
                idx = next_idx
            else:
                break

        return min(idx + 5, n - 1) if direction > 0 else max(idx - 5, 0)

    def is_interesting(self, pixel, saturation_threshold, low_brightness, high_brightness):
        # A pixel is interesting if:
        #  - It is non-gray (channel range > saturation_threshold)
        #  - Its average brightness is between low_brightness and high_brightness.

        if (np.max(pixel) - np.min(pixel)) <= saturation_threshold:
            return False
        brightness = np.mean(pixel)
        return low_brightness <= brightness <= high_brightness

    def move_to_interesting(self, frame, x, y, search_radius=10, extra_offset=5, saturation_threshold=10, low_brightness=30, high_brightness=225):
        # Within a search_radius around (x,y), find an "interesting" pixel, and then move extra_offset further
        # into that region along the same direction. Uses a vectorized approach for efficiency.

        H, W = frame.shape[:2]
        xmin = max(x - search_radius, 0)
        xmax = min(x + search_radius, W - 1)
        ymin = max(y - search_radius, 0)
        ymax = min(y + search_radius, H - 1)

        region = frame[ymin:ymax + 1, xmin:xmax + 1]
        channel_range = region.max(axis=-1) - region.min(axis=-1)
        brightness = region.mean(axis=-1)
        interesting_mask = (channel_range > saturation_threshold) & (brightness >= low_brightness) & (brightness <= high_brightness)

        if interesting_mask[y - ymin, x - xmin]:
            found_y, found_x = y, x
        else:
            coords = np.argwhere(interesting_mask)
            if coords.size == 0:
                return x, y
            coords[:, 0] += ymin  # adjust row indices
            coords[:, 1] += xmin  # adjust column indices
            dists = np.linalg.norm(coords - np.array([y, x]), axis=1)
            min_index = np.argmin(dists)
            found_y, found_x = coords[min_index]

        dx = found_x - x
        dy = found_y - y
        norm = math.hypot(dx, dy)
        if norm == 0:
            new_x = min(x + extra_offset, W - 1)
            new_y = y
        else:
            new_x = int(found_x + (dx / norm) * extra_offset)
            new_y = int(found_y + (dy / norm) * extra_offset)
            new_x = max(0, min(new_x, W - 1))
            new_y = max(0, min(new_y, H - 1))
        return new_x, new_y

    def move_to_prominent_color(self, frame, x, y, target_rgb, search_radius=10, extra_offset=5, color_threshold=30):
        # Within a search_radius around (x,y), find pixels similar to the target_rgb color,
        # and then move extra_offset further into that region along the same direction.

        # Parameters:
        # - frame: The image frame (numpy array)
        # - x, y: Current position coordinates
        # - target_rgb: The RGB color to look for [r, g, b]
        # - search_radius: Radius to search around (x,y)
        # - extra_offset: Additional distance to move in the direction of the found color
        # - color_threshold: Maximum color distance to consider a match

        # Returns:
        # - new_x, new_y: The new coordinates to move to

        H, W = frame.shape[:2]
        xmin = max(x - search_radius, 0)
        xmax = min(x + search_radius, W - 1)
        ymin = max(y - search_radius, 0)
        ymax = min(y + search_radius, H - 1)

        region = frame[ymin:ymax + 1, xmin:xmax + 1]

        # Calculate color distance (Euclidean distance in RGB space)
        target_rgb = np.array(target_rgb)
        color_distances = np.sqrt(np.sum((region - target_rgb) ** 2, axis=2))

        # Find pixels with similar color
        similar_color_mask = color_distances < color_threshold

        # Check if current position is within the region
        # and if it's already on a similar color
        local_y = y - ymin
        local_x = x - xmin

        if (0 <= local_y < similar_color_mask.shape[0] and
                0 <= local_x < similar_color_mask.shape[1] and
                similar_color_mask[local_y, local_x]):
            found_y, found_x = y, x
        else:
            # Find coordinates of similar colored pixels
            coords = np.argwhere(similar_color_mask)
            if coords.size == 0:
                return x, y  # No similar colors found, stay in place

            # Adjust coordinates back to the frame coordinate system
            coords[:, 0] += ymin  # adjust row indices
            coords[:, 1] += xmin  # adjust column indices

            # Find the closest similar colored pixel
            # Note: coords from argwhere are in [y, x] format (row, column)
            dists = np.linalg.norm(coords - np.array([y, x]), axis=1)
            min_index = np.argmin(dists)
            found_y, found_x = coords[min_index]

        # Calculate direction vector FROM current position TO the found color
        vector_to_color_x = found_x - x  # Positive: color is to the right, Negative: color is to the left
        vector_to_color_y = found_y - y  # Positive: color is below, Negative: color is above

        # Calculate distance to the found color
        distance = np.hypot(vector_to_color_x, vector_to_color_y)

        if distance == 0:
            # We're already at a pixel with the target color, move in a default direction
            new_x = min(x + extra_offset, W - 1)
            new_y = y
        else:
            # Calculate unit vector (direction only)
            unit_x = vector_to_color_x / distance
            unit_y = vector_to_color_y / distance

            # Move from current position in the direction of the color
            # Total movement = distance to color + extra_offset
            total_movement = distance + extra_offset
            new_x = int(x + unit_x * total_movement)
            new_y = int(y + unit_y * total_movement)

            # Ensure we stay within the frame bounds
            new_x = max(0, min(new_x, W - 1))
            new_y = max(0, min(new_y, H - 1))

        return new_x, new_y

    def detect_square_frame(self, region, canny_thresh1=50, canny_thresh2=150, min_area_ratio=0.1):
        if region is None or region.size == 0:
            return None
        gray = cv2.cvtColor(region, cv2.COLOR_BGR2GRAY)
        blurred = cv2.GaussianBlur(gray, (5, 5), 0)
        thresh = cv2.adaptiveThreshold(blurred, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 11, 2)
        edges = cv2.Canny(thresh, canny_thresh1, canny_thresh2)
        edges = cv2.dilate(edges, cv2.getStructuringElement(cv2.MORPH_RECT, (3, 3)), iterations=1)

        contours, _ = cv2.findContours(edges, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        H, W = region.shape[:2]
        area_thresh = min_area_ratio * H * W
        best_bbox, best_area = None, 0

        for cnt in contours:
            area = cv2.contourArea(cnt)
            if area < area_thresh:
                continue
            peri = cv2.arcLength(cnt, True)
            approx = cv2.approxPolyDP(cnt, 0.02 * peri, True)
            if len(approx) == 4 and cv2.isContourConvex(approx):
                x, y, w, h = cv2.boundingRect(approx)
                ar = w / h if h else 0
                if 0.8 <= ar <= 1.2 and area > best_area:
                    best_area, best_bbox = area, (x, y, w, h)

        return best_bbox

    def most_prominent_non_gray_color(self, rgb_array, gray_tol=20, bin_size=32):
        # gives each packet a prominent color to help identify its uniqueness, here's chatgpts yap:
        # Finds the most prominent non-gray/non-black color in an RGB image array by weighting pixels
        # that are more colorful (i.e. have a larger range among channels) and that are closer to the center.
        # Colors are binned (quantized) and the returned color is the center of the most weighted bin.

        # Parameters:
        #     rgb_array (np.ndarray): An array of shape (H, W, 3) representing an RGB image.
        #     gray_tol (int): A pixel is considered gray if the difference between its max and min channel is <= gray_tol.
        #     bin_size (int): The quantization step size for each channel.

        # Returns:
        #     np.ndarray: The prominent color as a 1D array [R, G, B] (dtype=np.uint8).

        H, W, _ = rgb_array.shape
        total_pixels = H * W

        # Convert pixels to int16 for safe arithmetic.
        pixels = rgb_array.reshape(-1, 3).astype(np.int16)

        # Create coordinate grid and compute spatial weights.
        # Pixel indices along height and width.
        y_indices, x_indices = np.indices((H, W))
        # Flatten coordinates to align with pixels.
        y_flat = y_indices.flatten()
        x_flat = x_indices.flatten()
        # Compute the center of the image.
        center_y, center_x = H / 2, W / 2
        # Euclidean distance from the center.
        distances = np.sqrt((y_flat - center_y) ** 2 + (x_flat - center_x) ** 2)
        # Normalize distances relative to the maximum distance.
        max_dist = np.sqrt(center_y ** 2 + center_x ** 2)
        spatial_weight = 1 - (distances / max_dist)  # Closer pixels get higher weight.

        # Compute color "vibrancy": how far apart the channels are.
        # Use the peak-to-peak difference (max - min) per pixel.
        diff = np.ptp(pixels, axis=1).astype(np.float32)
        # Normalize color difference (0 to 255).
        colorfulness = diff / 255.0

        # Also compute brightness (average channel value normalized to [0,1]).
        brightness = np.mean(pixels, axis=1) / 255.0

        # Combine factors: colorful pixels that are bright (i.e. not black) get higher weight.
        # This will naturally penalize both gray (low diff) and black (low brightness) pixels.
        color_weight = colorfulness * brightness

        # Combined weight per pixel: spatial weight multiplies the color weight.
        combined_weight = spatial_weight * color_weight

        # Optional: even if a pixel is "gray" (diff <= gray_tol), we could further reduce its weight.
        # Here, we reduce weight by half if diff <= gray_tol.
        combined_weight[diff <= gray_tol] *= 0.5

        # Quantize each pixel's color into bins.
        # For each channel, we map the value to the center of its bin.
        quantized = ((pixels // bin_size) * bin_size + bin_size // 2).clip(0, 255)

        # Sum the combined weights for each unique quantized color.
        # We use np.unique with return_inverse to aggregate the weights.
        quantized_view = quantized.view(np.dtype((np.void, quantized.dtype.itemsize * quantized.shape[1])))
        unique_colors, inverse = np.unique(quantized_view, return_inverse=True)
        unique_colors = unique_colors.view(quantized.dtype).reshape(-1, 3)

        # Sum the weights for pixels falling in each unique quantized bin.
        total_weights = np.zeros(unique_colors.shape[0], dtype=np.float64)
        np.add.at(total_weights, inverse, combined_weight)

        # Find the bin with the maximum total weight.
        best_bin_index = np.argmax(total_weights)
        prominent_color = unique_colors[best_bin_index].astype(np.uint8)

        r, g, b = prominent_color
        print(f"\033[48;2;{r};{g};{b}m   \033[0m Prominent color: [{r}, {g}, {b}]")
        return prominent_color

    def key_collector(self):
        """buttons get pressed and logged until released so the duration can be calculated"""

        def log_key_event(press_time, held_keys, duration, x, y, array, window_position, window_dimensions, flocation):
            self.active_keys.pop(held_keys[0])
            if held_keys[0] == 120:
                return
            key_data = copy.deepcopy(self.key_template_data)
            key_data.update({
                'time': press_time,
                'keys_held': held_keys,
                'duration': duration,
                'location': (x, y),
            })
            key_data['window_position'], key_data['window_dimensions'], key_data['flocation'], key_data['area'] = window_position, window_dimensions, flocation, array
            key_data['area'] = array
            if array is not None:
                key_data['prom_color'] = self.most_prominent_non_gray_color(array)
            if len(self.packets) > 0:
                current_pattern = [held_keys]
                # Add the current state to the pattern
                for i in range(min(4, len(self.packets))):
                    idx = len(self.packets) - 1 - i
                    if idx >= 0 and self.packets[idx].get("press") == "k":
                        current_pattern.append(self.packets[idx].get("keys_held", []))
                similarity = 0
                for packet_idx, packet in enumerate(self.packets):
                    if held_keys == "k":
                        # Retrograde factor - gives more weight to recent patterns
                        retro = packet_idx / len(self.packets)

                        # Look for repeating patterns of increasing length
                        for pattern_length in range(2, min(20, packet_idx + 1)):
                            # Get the pattern at current position
                            current_sequence = []
                            future_element = None

                            # Build the pattern we're checking for
                            for k in range(pattern_length):
                                idx = packet_idx - k
                                if idx >= 0 and self.packets[idx].get("press") == "k":
                                    current_sequence.insert(0, self.packets[idx].get("keys_held", []))

                            # Get the most recent occurrence of this pattern for comparison
                            recent_sequence = []
                            for k in range(pattern_length):
                                idx = len(self.packets) - 1 - k
                                if idx >= 0 and self.packets[idx].get("press") == "k":
                                    recent_sequence.insert(0, self.packets[idx].get("keys_held", []))

                            # If we found a matching pattern
                            if current_sequence == recent_sequence and len(current_sequence) > 0:
                                # Calculate pattern reward
                                pattern_reward = (pattern_length - 1) * 0.2 * retro

                                # Add distance bonus (smaller contribution now)
                                distance = math.sqrt((packet["flocation"][0] - key_data['flocation'][0]) ** 2 + (packet["flocation"][1] - key_data['flocation'][1]) ** 2)
                                distance_bonus = max(0, 0.1 * (1 - distance / self.max_distance))

                                # Add to similarity with pattern length bonus
                                similarity += min(1, pattern_reward + distance_bonus)
                            else:
                                break  # Break if pattern doesn't match

                # Normalize final significance
                location_signi = (similarity / len(self.packets))
            else:
                location_signi = 0
            key_data['signi'] = max(location_signi, self.area_signi(key_data['prom_color']))
            with self.file_lock:
                insort(self.packets, key_data, key=lambda x: x["time"])
                self.action_rate.append(key_data['signi'])
                with open(self.p_binary_data_path, 'ab') as file:
                    self.write_chunk(file, dill.dumps(key_data, protocol=5))

        def on_key_event(key):
            global time_cooldown, replaying_packets, macro_listening
            if macro_listening and cfg.enable_super_macro and cfg.capture_keyboard and not replaying_packets:
                hotkey_strings = [hk.strip() for hk in cfg.hotkey_macro_listen.split(',')]
                keycodes = []
                for key_str in hotkey_strings:
                    codes = keyboard.key_to_scan_codes(key_str)
                    if codes:
                        keycodes.extend(codes)
                if key.scan_code in keycodes:
                    return

                hotkey_strings = [hk.strip() for hk in cfg.hotkey_macro_intervene.split(',')]
                keycodes = []
                for key_str in hotkey_strings:
                    codes = keyboard.key_to_scan_codes(key_str)
                    if codes:
                        keycodes.extend(codes)
                if key.scan_code in keycodes:
                    return

                # Pass the scan code directly
                if key.event_type == 'down':
                    kc = key.scan_code
                    threading.Thread(target=on_press, args=(kc,)).start()
                else:
                    kc = key.scan_code
                    threading.Thread(target=on_release, args=(kc,)).start()

        def scancode_to_vk(scan_code):
            user32 = ctypes.WinDLL('user32', use_last_error=True)
            MapVirtualKeyW = user32.MapVirtualKeyW
            MapVirtualKeyW.argtypes = [wintypes.UINT, wintypes.UINT]
            MapVirtualKeyW.restype = wintypes.UINT
            return MapVirtualKeyW(scan_code, 1)

        def on_press(scan_code):
            global old_xy
            keyc = scancode_to_vk(scan_code)
            current_time = time.time()
            if keyc in {27, 0}:
                return
            if keyc not in self.active_keys:
                x, y = zhmiscellany.macro.get_mouse_xy()
                if not (0 <= x < self.monitor_x and 0 <= y < self.monitor_y):
                    return
                window_position, window_dimensions = self.get_focused_window_info()
                try:
                    floc = (int(((x - window_position[0]) / window_dimensions[0]) * self.monitor_x), int(((y - window_position[1]) / window_dimensions[1]) * self.monitor_y))
                except Exception:
                    return
                if floc in self.monitor_center:
                    return
                try:
                    if any(old_xy):
                        return
                except Exception:
                    return
                self.active_keys[keyc] = (current_time, x, y, self.area_screenshot(x, y), window_position, window_dimensions, floc)

        def on_release(scan_code):
            keyc = scancode_to_vk(scan_code)
            current_time = time.time()
            if keyc in self.active_keys:
                press_time = self.active_keys[keyc][0]
                log_key_event(press_time, [keyc], current_time - press_time, self.active_keys[keyc][1], self.active_keys[keyc][2], self.active_keys[keyc][3], self.active_keys[keyc][4], self.active_keys[keyc][5], self.active_keys[keyc][6])

        kb.hook(on_key_event)
        kb.wait()

    def mouse_collector(self):

        # Oh. Oh God. Oh God. Oh God.
        # Oh my God.
        # Holy mother of God.
        # Oh. Oh. Oh. Oh God.

        # B::::::::D
        def on_click(down_xy, button_number, duration, up_xy, first_area, window_position, window_dimensions, flocation):
            global time_cooldown
            click_data = copy.deepcopy(self.mouse_template_data)
            click_data.update({
                'mouse_button': button_number,
                'time': time.time() - duration,
                'location': down_xy,
                'location2': up_xy,
                'duration': duration,
            })
            click_data['window_position'], click_data['window_dimensions'], click_data['flocation'], click_data['area'] = window_position, window_dimensions, flocation, first_area
            if first_area is not None: click_data['prom_color'] = self.most_prominent_non_gray_color(first_area)
            try:
                click_data['flocation2'] = (int(((up_xy[0] - window_position[0]) / window_dimensions[0]) * self.monitor_x), int(((up_xy[1] - window_position[1]) / window_dimensions[1]) * self.monitor_y))
            except:
                return
            similarity, mouse_packets = 0, 0
            if len(self.packets) > 0:
                for packet in self.packets:
                    try:
                        if packet["press"] == "m":
                            distance = math.sqrt((packet["flocation"][0] - click_data['flocation'][0]) ** 2 + (packet["flocation"][1] - click_data['flocation'][1]) ** 2)
                            similarity += max(0, 1 - distance / self.max_distance)
                            mouse_packets += 1
                    except:
                        z.l('error', packet)
                area_signi = self.area_signi(click_data['prom_color'])
                try:
                    click_data['signi'] = max(math.sqrt(similarity / mouse_packets), area_signi)
                except:
                    click_data['signi'] = 0
            with self.file_lock:
                insort(self.packets, click_data, key=lambda x: x["time"])
                self.action_rate.append(click_data['signi'])
                with open(self.p_binary_data_path, 'ab') as file:
                    self.write_chunk(file, dill.dumps(click_data, protocol=5))
                threading.Thread(target=self.quick_pattern_intervene, args=(click_data,)).start()

        # captures mouse scrolls
        def on_scroll(x, y, dy):
            global time_cooldown
            scroll_data = copy.deepcopy(self.scroll_template_data)
            scroll_data.update({
                'direction': round(dy),
                'time': time.time(),
                'location': (x, y),
            })
            scroll_data['window_position'], scroll_data['window_dimensions'] = self.get_focused_window_info()
            try:
                scroll_data['flocation'] = (int(((x - scroll_data['window_position'][0]) / scroll_data['window_dimensions'][0]) * self.monitor_x), int(((y - scroll_data['window_position'][1]) / scroll_data['window_dimensions'][1]) * self.monitor_y))
            except:
                return
            if scroll_data['flocation'] in self.monitor_center: return
            scroll_data['area'] = self.area_screenshot(x, y)
            if scroll_data['area'] is not None: scroll_data['prom_color'] = self.most_prominent_non_gray_color(scroll_data['area'])
            similarity, scroll_packets = 0, 0
            if len(self.packets) > 0:
                for packet in self.packets:
                    if packet["press"] == "s":
                        distance = math.sqrt((packet["flocation"][0] - scroll_data['flocation'][0]) ** 2 + (packet["flocation"][1] - scroll_data['flocation'][1]) ** 2)
                        similarity += max(0, 1 - distance / self.max_distance)
                        scroll_packets += 1
                try:
                    scroll_data['signi'] = (math.sqrt(similarity / scroll_packets) + self.area_signi(scroll_data['area'])) / 2
                except:
                    scroll_data['signi'] = 0
            with self.file_lock:
                insort(self.packets, scroll_data, key=lambda x: x["time"])
                self.action_rate.append(scroll_data['signi'])
                with open(self.p_binary_data_path, 'ab') as file:
                    self.write_chunk(file, dill.dumps(scroll_data, protocol=5))

        class MouseHook:
            def __init__(self, click_hook, scroll_hook, area_screenshot, monitor_center, monitor_x, monitor_y, get_focused_window_info):
                self.event_queue = []
                self.running = True
                self.process_thread = threading.Thread(target=self._process_events)
                self.process_thread.daemon = True
                self.process_thread.start()
                self.click_hook = click_hook
                self.scroll_hook = scroll_hook
                self.area_screenshot = area_screenshot
                self.monitor_center = monitor_center
                self.monitor_x = monitor_x
                self.monitor_y = monitor_y
                self.get_focused_window_info = get_focused_window_info
                self.last_position = False
                self.xy = zhmiscellany.misc.get_mouse_xy()  # Initialize xy as an instance attribute
                self.next_capture = 0
                self.mouses = [[], [], [], []]
                self._dc_w = ctypes.windll.user32.GetSystemMetrics(36)
                self._dc_h = ctypes.windll.user32.GetSystemMetrics(37)
                self.last_click_pos = None
                self.window_position, self.window_dimensions = self.get_focused_window_info()
                # self.mouses = [(time.time(), (0, 0), self.crop_screenshot(200, 200))] * 4  # random values to initilize, shouldn't matter very much
                mouse.hook(self.on_event)
                self.old_loc_upd = threading.Thread(target=self.old_loc)
                self.old_loc_upd.daemon = True
                self.old_loc_upd.start()

            def old_loc(self):
                global old_xy
                old_xy = deque(maxlen=5)  # automatically keeps only the last 5 entries
                while True:
                    window_position, window_dimensions = self.get_focused_window_info()
                    if window_position is not None:
                        x, y = zhmiscellany.misc.get_mouse_xy()
                        floc = (int(((x - window_position[0]) / window_dimensions[0]) * self.monitor_x), int(((y - window_position[1]) / window_dimensions[1]) * self.monitor_y))
                        old_xy.append(floc in self.monitor_center)
                    time.sleep(0.01)

            def _process_events(self):
                while self.running:
                    try:
                        # Process events from queue
                        data = self.event_queue.pop(0)
                        zhmiscellany.processing.start_daemon(target=data[0], args=data[1])
                    except:
                        time.sleep(0.05)

            def down(self, button_number):
                dur = time.time()
                bebos = self.xy
                if not (0 <= bebos[0] < self.monitor_x and 0 <= bebos[1] < self.monitor_y):
                    return
                if bebos == (0, 0):
                    return
                wp, wd = self.get_focused_window_info()
                try:
                    floc = (int(((bebos[0] - wp[0]) / wd[0]) * self.monitor_x), int(((bebos[1] - wp[1]) / wd[1]) * self.monitor_y))
                    if floc in self.monitor_center or any(old_xy):
                        self.mouses[button_number] = []
                        return
                except:
                    self.mouses[button_number] = []
                    return
                self.mouses[button_number] = (dur, bebos, self.area_screenshot(*self.xy), wp, wd, floc)

            def up(self, button_number):
                if self.mouses[button_number]:
                    down_time, down_pos, *rest = self.mouses[button_number]
                    elapsed = time.time() - down_time
                    self.click_hook(down_pos, button_number, elapsed, self.xy, *rest)
                    # record last click location for next double-click test
                    self.last_click_pos = down_pos
                    self.mouses[button_number] = []

            def double(self, button_number):
                bebos = self.xy
                # if the first click was too far away, ignore this “double”
                if self.last_click_pos is not None:
                    dx = abs(bebos[0] - self.last_click_pos[0])
                    dy = abs(bebos[1] - self.last_click_pos[1])
                    if dx > self._dc_w or dy > self._dc_h:
                        return
                # … your existing bounds-and-focus checks …
                wp, wd = self.get_focused_window_info()
                try:
                    floc = (int(((bebos[0] - wp[0]) / wd[0]) * self.monitor_x), int(((bebos[1] - wp[1]) / wd[1]) * self.monitor_y))
                    if floc in self.monitor_center or any(old_xy):
                        self.mouses[button_number] = []
                        return
                except:
                    self.mouses[button_number] = []
                    return
                self.click_hook(
                    bebos, button_number, 0.07,
                    bebos, self.area_screenshot(bebos[0], bebos[1]),
                    wp, wd, floc,
                )
                self.mouses[button_number] = []

            def wheel(self, delta):
                dy = delta
                bebos = self.xy
                if not (0 <= bebos[0] < self.monitor_x and 0 <= bebos[1] < self.monitor_y):
                    return
                self.scroll_hook(*bebos, dy)

            def on_event(self, event):
                global time_cooldown, replaying_packets, old_xy, macro_listening
                if replaying_packets:
                    self.mouses = [[], [], [], []]
                elif macro_listening and cfg.enable_super_macro:
                    match type(event):
                        case mouse.ButtonEvent:
                            if cfg.capture_clicks:
                                match event.button:
                                    case 'left':
                                        button_number = 1
                                    case 'right':
                                        button_number = 2
                                    case 'middle':
                                        button_number = 3
                                    case _:
                                        return
                                if event.event_type == 'double':
                                    threading.Thread(target=self.double, args=(button_number,)).start()
                                if event.event_type == 'down':
                                    threading.Thread(target=self.down, args=(button_number,)).start()
                                else:
                                    threading.Thread(target=self.up, args=(button_number,)).start()
                        case mouse.WheelEvent:
                            if cfg.capture_mouse_scrolls:
                                threading.Thread(target=self.wheel, args=(event.delta,)).start()
                        case mouse.MoveEvent:
                            self.xy = (event.x, event.y)

        # this class is not blocking since mouse.hook is not blocking, so after this line this thread terminates
        MouseHook(click_hook=on_click, scroll_hook=on_scroll, area_screenshot=self.area_screenshot, monitor_center=self.monitor_center, monitor_x=self.monitor_x, monitor_y=self.monitor_y, get_focused_window_info=self.get_focused_window_info)

    def find_gaps(self, numbers):
        return [numbers[i] - numbers[i - 1] for i in range(1, len(numbers))]

    def get_arr2(self, frame):
        rv = frame['rgb']
        return np.array(rv) if isinstance(rv, (list, np.ndarray)) else self.frame_hashes[frame['hash']]

    def compare_arrays(self, arr1, frames, mask=None):
        tol = 10
        ct, st = time.time() - 3.0, time.time() + 0.1
        fs = {}  # stores frame similarities
        if mask is None:
            # First pass: look for a frame with reward > 0.5 to generate a blurred mask.
            for frame in frames:
                if time.time() > st: break
                if frame['time'] > ct: continue
                if frame['hash'] in self.frame_hashes:
                    arr2 = self.frame_hashes[frame['hash']]
                else:
                    continue
                if arr1.shape != arr2.shape:
                    continue

                diff = np.abs(arr1 - arr2)
                cs = 1 - (diff / tol)
                cs[diff > tol] = 0
                reward = np.sum(cs) / np.prod(arr1.shape)

                if reward > 0.5:
                    # Compute a 1-channel mask (values in [0.0, 1.0])
                    mask = np.clip(np.mean(1 - (diff / tol), axis=-1), 0.0, 1.0)
                    mask[diff.max(axis=-1) > tol] = 0
                    mask = cv2.GaussianBlur(mask, (5, 5), 0)
                    # Remove isolated low-value pixels:
                    local_avg = cv2.blur(mask, (3, 3))
                    mask[(mask < 0.5) & (local_avg < 0.5)] = 0.0

                    # Ensure mask covers at most 50% of the screen
                    mask_coverage = np.sum(mask > 0) / mask.size
                    if mask_coverage > 0.5:
                        # Sort mask values and keep only the top 50%
                        threshold = np.sort(mask.flatten())[int(mask.size * 0.5)]
                        mask[mask < threshold] = 0.0

                    break
                else:
                    fs[reward] = frame['time']
            if mask is None:
                return fs, mask

            # Second pass: compare arr1 and each arr2 only in the masked regions.
            fs = {}
            for frame in frames:
                if frame['time'] > ct: continue
                if frame['hash'] in self.frame_hashes:
                    arr2 = self.frame_hashes[frame['hash']]
                else:
                    continue
                if arr1.shape != arr2.shape:
                    continue

                diff = np.abs(arr1 - arr2)
                cs = 1 - (diff / tol)
                cs[diff > tol] = 0
                cs_avg = np.mean(cs, axis=-1)
                total = np.sum(mask)
                masked_reward = np.sum(cs_avg * mask) / total if total else 0.0
                fs[masked_reward] = frame['time']
            return fs, mask
        elif mask is False:
            diff = np.abs(arr1 - frames)
            cs = 1 - (diff / tol)
            cs[diff > tol] = 0
            reward = np.sum(cs) / np.prod(arr1.shape)
            return reward >= 0.16
        else:
            diff = np.abs(arr1 - frames)
            cs = 1 - (diff / tol)
            cs[diff > tol] = 0
            cs_avg = np.mean(cs, axis=-1)
            total = np.sum(mask)
            masked_reward = np.sum(cs_avg * mask) / total if total else 0.0
            return masked_reward >= 0.16

    def sort_groups(self, flat, groups):
        """tries sorting each packet by where it tends to show up in the origional memories relative to the start of the memory"""
        get_time = lambda x: x['time'] if isinstance(x, dict) else x[0]['time']
        anchor_by_id = {(id(item) if isinstance(item, dict) else id(item[0])): group[0] for group in groups for item in group}
        anchors, extras = [], []
        for item in flat:
            value, extra = (item, None) if isinstance(item, dict) else (item[0], item[1])
            anchor = anchor_by_id.get(id(value), value)
            if value == anchor:
                anchors.append((value, extra) if extra is not None else value)
            else:
                diff = abs(get_time(anchor) - value['time'])
                extras.append((diff, (value, extra) if extra is not None else value))
        extras.sort(key=lambda x: x[0])
        return anchors[::-1] + [x[1] for x in extras]

    def merge_overlapping_packets(self, flat):
        """merges actions tht likely occured at the same time"""
        unit_packets = []
        sorted_packets = sorted(flat, key=lambda p: p['time'])
        if sorted_packets:
            current_group = [sorted_packets[0]]
            current_end = sorted_packets[0]['time'] + sorted_packets[0].get('duration', 0.2)
            for packet in sorted_packets[1:]:
                packet_start = packet['time']
                packet_duration = packet.get('duration', 0.2)
                packet_end = packet_start + packet_duration
                if packet_start <= current_end:
                    current_group.append(packet)
                    current_end = max(current_end, packet_end)
                else:
                    if len(current_group) == 1:
                        unit_packets.append(current_group[0])
                    else:
                        unit_packets.append(tuple(current_group))
                    current_group = [packet]
                    current_end = packet_end
            if current_group:
                if len(current_group) == 1:
                    unit_packets.append(current_group[0])
                else:
                    unit_packets.append(tuple(current_group))
        return unit_packets

    def find_median_gaps(self, replay_packets):
        median_gaps = []
        for packets_a in replay_packets:
            if len(packets_a) > 1:
                times = [packet['time'] for packet in packets_a]
                time_differences = self.find_gaps(times)
                n = len(time_differences)
                mid = n // 2
                median_gap = time_differences[mid] if n % 2 else (time_differences[mid - 1] + time_differences[mid]) / 2
                if median_gap >= 1.5:
                    median_gap = 1.5
                elif median_gap <= 0.55:
                    median_gap = 0.55
                median_gaps.append(median_gap)
        n = len(median_gaps)
        mid = n // 2
        if median_gaps:
            median_gap = (median_gaps[mid] if n % 2 else (median_gaps[mid - 1] + median_gaps[mid]) / 2) + 0.2
        else:
            median_gap = 0.75
        return median_gap

    def merge_alike_packets(self, group):
        # Precompute histograms for each packet's 'area'
        histograms = [self.compute_histogram(packet['area']) for packet in group]

        # List of indices of packets to be kept.
        selected_indices = []
        # A flag array to record if the packet already has a duplicate (repeat).
        has_repeat = [False] * len(group)
        # Dictionary to store alternate areas for each kept packet index.
        alternate_areas = {}

        # Iterate over each packet index.
        for i in range(len(group)):
            duplicate_found = False
            # Compare the current packet to all previously selected packets.
            for idx in selected_indices:
                if self.are_arrays_similar([histograms[i], histograms[idx]], hist_similarity_threshold=0.7) or self.are_rgbs_similar([group[i], group[idx]]):
                    # Mark the already selected packet as having duplicates.
                    has_repeat[idx] = True
                    duplicate_found = True
                    # Append the removed packet's 'area' to the alternate_areas list for that kept packet index.
                    if idx not in alternate_areas:
                        alternate_areas[idx] = [group[i]['area']]
                    else:
                        alternate_areas[idx].append(group[i]['area'])
                    break
            # Only add packet i if no similar packet has been seen yet.
            if not duplicate_found:
                selected_indices.append(i)

        # Build the new group using the selected indices.
        new_group = []
        new_histograms = []
        for idx in selected_indices:
            packet = group[idx]
            # If a duplicate was found for this packet, mark its 'repeat' key and assign its alternate areas.
            if has_repeat[idx]:
                packet['repeat'] = True
                if 'alternate_areas' in packet:
                    packet['alternate_areas'].extend(alternate_areas.get(idx, []))
                else:
                    packet['alternate_areas'] = alternate_areas.get(idx, [])
            new_group.append(packet)
            new_histograms.append(histograms[idx])

        repeated = sum(1 for packet in new_group if 'repeat' in packet)
        return new_group, new_histograms

    def screen_intervene(self):
        """compares rgb arrays to know when it's appropriate to intervene with an idea, then converges all memories of what happened at those prior points to replay the memory more seamlessly.
        This is good for automating edge cases that may occur for certain tasks"""
        global time_cooldown, replaying_packets, macro_listening, latest_location, latest_location2, latest_location3
        next_capture_time = time.time()
        while True:
            if cfg.enable_macro_intervene and cfg.enable_super_macro and not any(old_xy) and time.time() >= next_capture_time and self.recent_frame_p is not None and time_cooldown <= time.time() and self.packets and not replaying_packets:
                recent_frame = self.recent_frame_p
                # region frame_similarities, compare_mask = self.compare_arrays(recent_frame, self.frames) UnboundLocalError: local variable 'recent_frame' referenced before assignment
                frame_similarities, compare_mask = self.compare_arrays(recent_frame, self.frames)
                sorted_keys = sorted((k for k in frame_similarities if k > 0.5), reverse=True)
                purged_frame_similarities = []
                selected_times = []
                # remove overlapping times
                for k in sorted_keys:
                    current_time = frame_similarities[k]
                    if all(abs(current_time - t) >= 2 for t in selected_times):
                        purged_frame_similarities.append(current_time)
                        selected_times.append(current_time)
                replay_packets = []
                purged_frame_similarities = purged_frame_similarities[:15]
                for frame_incident_time in purged_frame_similarities:
                    packets_around = []
                    # finds closest packet to incident time
                    closest_packet = bisect([packet['time'] for packet in self.packets], frame_incident_time) - 1
                    if closest_packet >= 0:
                        z.l(closest_packet, len(self.packets))
                        incident_time = self.packets[closest_packet]['time']

                        if abs(incident_time - frame_incident_time) >= 1.5: continue
                        # tries seeing if there's any packets that happened before the supposed incident time so the closest packet is more accurate to the start of the sequential sequence. rewind time
                        while True:
                            if closest_packet <= 0: break
                            if (self.packets[closest_packet - 1]['signi'] ** 0.3 >= cfg.macro_intervene_threshold) and ((self.packets[closest_packet - 1]['time'] - incident_time) >= -1):
                                closest_packet -= 1
                                incident_time = self.packets[closest_packet]['time']
                            else:
                                break
                    else:
                        break
                    # now that the closest packet to when the true incident probably started, we can now start finding all of what happened during the incident and cut off when the sequence ends
                    packets_around.append(self.packets[closest_packet])
                    time_cutoff = self.packets[closest_packet]['time']
                    i = closest_packet + 1
                    try:
                        for j in range(min(10, len(self.packets))):
                            retro = 1  # 0.9 ** (closest_packet - i)
                            elapsed_time = self.packets[i]['time'] - time_cutoff
                            current_packet = self.packets[i]['signi'] * retro
                            if (current_packet ** 0.5 >= cfg.macro_intervene_threshold) and ((self.packets[i]['time'] - time_cutoff) <= 1):
                                packets_around.append(self.packets[i])
                                time_cutoff = self.packets[i]['time']
                                i += 1
                                if i > len(self.packets):
                                    break
                            else:
                                break
                    except:
                        pass
                    replay_packets.append(packets_around)
                # we don't want sequences of just 1 or less
                if len(replay_packets) < 1:
                    next_capture_time += cfg.intervene_rate
                    continue
                print("intervene")
                median_gap = self.find_median_gaps(replay_packets)
                self.titty = random.randint(0, 9999)
                flat, hist = [], []
                for i in replay_packets:
                    flats, histt = self.merge_alike_packets(i)
                    for i in flats:
                        flat.append(i)
                    for i in histt:
                        hist.append(i)
                flat = [i for i in flat if i['time'] not in self.bad_packets]
                flat.sort(key=lambda x: x['time'])
                flat = self.remove_similar_areas(flat, hist)
                if isinstance(flat, dict):
                    flat = list(flat)
                unit_packets = self.merge_overlapping_packets(flat)
                unit_packets = self.sort_groups(unit_packets, replay_packets)
                tickleable_threads = []
                for packet in unit_packets:
                    if time.time() <= time_cooldown: break
                    items = packet if isinstance(packet, tuple) else (packet,)
                    self.thread_com = {}
                    for i in items:
                        self.thread_com[i['time']] = False
                        t = threading.Thread(target=self.replay_actions, args=(i, 1 / self.actions_per_second, median_gap,), kwargs={'recent_frame': recent_frame, 'recent_frame_mask': compare_mask})
                        tickleable_threads.append(t)
                        t.start()
                    while 'finished' not in self.thread_com and time_cooldown <= time.time() and 'done' not in self.thread_com:
                        time.sleep(0.01)
                    if 'done' in self.thread_com: break
                if tickleable_threads:  # waits for all replay_actions threads to finish before returning the cursor
                    for t in tickleable_threads:
                        t.join()
                    # zhmiscellany.misc.click_pixel(pt, act_start=False, act_end=False)
                    time_cooldown = time.time() + 2
                replaying_packets = False
                latest_location = None
                latest_location2 = None
                latest_location3 = None
                if not replaying_packets and macro_listening: self.back_to_listen()
                if not macro_listening: self.turn_off()
                next_capture_time += cfg.intervene_rate
            time.sleep(0.025)

    # region cursor array similarity intervene

    def quick_pattern_intervene(self, og_packet):
        """if recent packet arrays are similar they're probably clicking on something repetitive, so we can likely intervene"""
        if cfg.enable_macro_intervene and len(self.packets) >= 3 and cfg.enable_super_macro:
            global time_cooldown, replaying_packets, macro_listening, latest_location, latest_location2, latest_location3
            recent_packets = self.packets[-3:-1]
            e = all(self.are_arrays_similar(first_array=og_packet['area'], second_array=i['area']) for i in recent_packets)
            if e and time.time() > time_cooldown and not replaying_packets:
                altered_og_packet = copy.deepcopy(og_packet)
                areas = []
                for i in recent_packets:
                    areas.append(i['area'])
                altered_og_packet['alternate_areas'] = areas
                recent_packets.append(og_packet)
                median_gap = self.find_median_gaps([recent_packets])
                recent_frame = self.recent_frame_p
                z.l('quick intervene')
                self.replay_actions(altered_og_packet, 1 / self.actions_per_second, median_gap, repeat_memory=True, recent_frame=recent_frame, cerf_packets=recent_packets)
                latest_location = None
                latest_location2 = None
                latest_location3 = None
                replaying_packets = False
                if not replaying_packets and macro_listening: self.back_to_listen()
                if not macro_listening: self.turn_off()

    def create_mask(self, replay_packet, cerf_packets):
        """gathers a general idea of where the object typically is on screen, so if there's identical objects outside this area, we don't click on it to avoid unwanted actions"""
        replay_packet = copy.deepcopy(replay_packet)
        grid = np.zeros((10, 10))
        points = 1
        similar = []
        # figure out how many similar packets there are
        ct = time.time() + 0.02
        for packet in self.packets:
            if ct > time.time():
                if packet in cerf_packets or self.are_arrays_similar(first_array=replay_packet['area'], second_array=packet['area']):
                    similar.append(packet)
            else:
                break
        # depending on length, we want that having an effect on how spread out the points are, so if it's less certain it's more willing to be generous to the mask
        if len(similar) == 1:
            spread = 4
        # elif 2 <= len(similar) <= 4:
        #     spread = 3
        else:
            spread = 3
        for packet in similar:
            y, x = round(packet['flocation'][0] / (self.monitor_x - 1) * (10 - 1)), round(packet['flocation'][1] / (self.monitor_y - 1) * (10 - 1))
            strength = 1.0 / points
            for z in range(-spread, spread + 1):
                for j in range(-spread, spread + 1):
                    nx, ny = x + z, y + j
                    if 0 <= nx < 10 and 0 <= ny < 10:
                        distance = (z ** 2 + j ** 2) ** 0.5 / spread
                        grid[nx][ny] += strength * max(0, 1 - distance)
            grid = np.clip(grid, 0, 1)
            points += 1
        return grid

    def convert_cropped_to_screen(self, cropped_point, crop_origin):
        x_cropped, y_cropped = cropped_point
        first_row, first_col = crop_origin
        x_actual = first_col + x_cropped
        y_actual = first_row + y_cropped
        return (x_actual, y_actual)

    def replay_actions(self, packet, extra_hold_time, median_gap, repeat_memory=False, recent_frame=None, recent_frame_mask=False, cerf_packets=[]):
        global latest_location, latest_location2, latest_location3, time_cooldown, replaying_packets
        window_position, window_dimensions = self.get_focused_window_info()
        weight = packet.get('weight')
        majority = False
        if weight:
            if weight >= 0.6:
                majority = True
        if 'repeat' in packet or majority:
            repeat_memory = True
        if packet['area'] is not None:
            mask = self.create_mask(packet, cerf_packets)
            # precompute values that don't change during the loop
            # h, w = packet['area'].shape[:2]
            if 'repeat' in packet:
                item_frequency = 5
            elif 'weight' in packet:
                if packet['weight'] == 1:
                    item_frequency = 10
                else:
                    item_frequency = max(int(str(round(packet['weight'], 1))[2]), 4)
            else:
                item_frequency = 5
        while True:
            cut_off_time = time.time() + median_gap
            if packet['area'] is not None and not cfg.strict_location:
                if 'alternate_areas' in packet:
                    i = (0, len(packet['alternate_areas']))
                else:
                    i = (0, 0)
                while True:
                    if time.time() >= cut_off_time or time.time() <= time_cooldown:
                        self.broke_out_becauseofmedian += 1
                        latest_location = None
                        latest_location2 = None
                        latest_location3 = None
                        self.thread_com['finished'] = True
                        return
                    if repeat_memory:
                        screen_rgb = self.get_screen_pixels()
                    else:
                        screen_rgb = self.get_screen_pixels(True)
                    if recent_frame is not None:
                        s_screen_rgb = cv2.resize(screen_rgb, self.target_resolution, interpolation=cv2.INTER_LANCZOS4)
                        if not self.compare_arrays(recent_frame, s_screen_rgb, recent_frame_mask):
                            self.thread_com['done'] = True
                            latest_location = None
                            latest_location2 = None
                            latest_location3 = None
                            return
                    # minimizing search area by carving a new array using the mask
                    scaled_mask = resize(mask, screen_rgb.shape[:2], anti_aliasing=True)
                    above_threshold_rows = np.where(np.any(scaled_mask > 0.5, axis=1))[0]
                    if len(above_threshold_rows) != 0:
                        raw_first_row, raw_last_row = above_threshold_rows[0], above_threshold_rows[-1]
                        above_threshold_cols = np.where(np.any(scaled_mask > 0.5, axis=0))[0]
                        raw_first_col, raw_last_col = above_threshold_cols[0], above_threshold_cols[-1]

                        # Calculate margins as 10% of the screen dimensions
                        margin_row = int(screen_rgb.shape[0] * 0.05)
                        margin_col = int(screen_rgb.shape[1] * 0.05)
                        # if repeat_memory:
                        #     margin_row = int(screen_rgb.shape[0] * 0.05)
                        #     margin_col = int(screen_rgb.shape[1] * 0.05)
                        # else:
                        #     margin_row = int(screen_rgb.shape[0] * 0.01)
                        #     margin_col = int(screen_rgb.shape[1] * 0.01)

                        # Expand the raw boundaries using the computed margins, ensuring we stay within image bounds
                        first_row = max(0, raw_first_row - margin_row)
                        last_row = min(screen_rgb.shape[0] - 1, raw_last_row + margin_row)
                        first_col = max(0, raw_first_col - margin_col)
                        last_col = min(screen_rgb.shape[1] - 1, raw_last_col + margin_col)
                        screen_rgb_c = screen_rgb[first_row:last_row + 1, first_col:last_col + 1, :]
                    else:
                        self.thread_com['finished'] = True
                        latest_location = None
                        latest_location2 = None
                        latest_location3 = None
                        return
                    if i[1] == 0:
                        pattern_rgb = packet['area']
                    else:
                        index = (i[0]) % len(packet['alternate_areas'])
                        pattern_rgb = packet['alternate_areas'][index]
                        if i[0] + 1 == i[1]:
                            i = (0, i[1])
                        else:
                            i = (i[0] + 1, i[1])
                    h, w, _ = pattern_rgb.shape
                    left = np.random.randint(0, int(0.1 * w) + 1)
                    right = np.random.randint(0, int(0.1 * w) + 1)
                    up = np.random.randint(0, int(0.1 * h) + 1)
                    bottom = np.random.randint(0, int(0.1 * h) + 1)
                    pattern_rgb = pattern_rgb.astype(np.float32)
                    pattern_rgb = pattern_rgb[up:h - bottom or None, left:w - right or None]
                    # Convert to float32 for consistency
                    screen_rgb_c = screen_rgb_c.astype(np.float32)
                    # Compute template matching for each channel
                    responses = []
                    for ch in range(3):
                        res = cv2.matchTemplate(screen_rgb_c[:, :, ch], pattern_rgb[:, :, ch], cv2.TM_CCOEFF_NORMED)
                        responses.append(res)
                    # Stack channel results along a new axis (shape: [height, width, channels])
                    responses = np.stack(responses, axis=-1)
                    # Use the median over channels as the final matching response
                    result = np.median(responses, axis=-1)
                    # Flatten the result if needed for subsequent processing
                    values = result.flatten()
                    num_results = 10
                    flat_indices = np.argpartition(values, -num_results)[-num_results:]
                    flat_indices = flat_indices[np.argsort(values[flat_indices])[::-1]]
                    top_locs = np.unravel_index(flat_indices, result.shape)
                    top_values = result[top_locs]
                    matches = list(zip(top_values, zip(top_locs[0], top_locs[1])))
                    point_values = []
                    for match in matches:
                        x, y = self.convert_cropped_to_screen((match[1][1], match[1][0]), (first_row, first_col))
                        center_x = int(x + w // 2)
                        center_y = int(y + h // 2)
                        center_x, center_y = self.scale_outwards(center_x, center_y)
                        x_ad, y_ad = round(center_x / (self.monitor_x - 1) * (10 - 1)), round(center_y / (self.monitor_y - 1) * (10 - 1))
                        point_values.append((min(match[0], mask[y_ad, x_ad]), (center_x, center_y)))
                    max_val = max(point_values, key=lambda t: t[0])
                    if max_val[0] <= 0.55:
                        continue
                    else:
                        location = max_val[1][0], max_val[1][1]
                        break
            else:
                if window_position == packet['window_position'] and window_dimensions == packet['window_dimensions']:
                    location = packet['location']
                else:
                    location = (int((packet['flocation'][0] / self.monitor_x) * window_dimensions[0] + window_position[0]), int((packet['flocation'][1] / self.monitor_y) * window_dimensions[1] + window_position[1]))
            if location is None:
                self.thread_com['finished'] = True
                latest_location = None
                latest_location2 = None
                latest_location3 = None
                return
            x, y = zhmiscellany.misc.get_mouse_xy()
            if 'prom_color' in packet and not cfg.strict_location:
                ix, iy = self.scale_inwards(location[0], location[1])
                ix, iy = self.move_to_prominent_color(screen_rgb, ix, iy, packet['prom_color'])
                ix, iy = self.scale_outwards(ix, iy)
                location = (ix, iy)
            if latest_location is not None and latest_location2 is not None and latest_location3 is not None:
                dx = location[0] - latest_location[0]
                dy = location[1] - latest_location[1]
                if abs(dx) + abs(dy) >= self.max_distance / 2 and not cfg.strict_location:
                    quarter = self.max_distance // 3
                    dx_min = max(-quarter, -location[0])
                    dx_max = min(quarter, self.monitor_x - location[0])
                    dy_min = max(-quarter, -location[1])
                    dy_max = min(quarter, self.monitor_y - location[1])
                    location = (location[0] + random.randint(dx_min, dx_max), location[1] + random.randint(dy_min, dy_max))
                if self.intervene_disrupt < time.time():
                    mdx = x - latest_location[0]
                    mdy = y - latest_location[1]
                    mdx2 = x - latest_location2[0]
                    mdy2 = y - latest_location2[1]
                    mdx3 = x - latest_location3[0]
                    mdy3 = y - latest_location3[1]
                    if abs(mdx) + abs(mdy) >= self.max_distance / 0.7 and abs(mdx2) + abs(mdy2) >= self.max_distance / 0.7 and abs(mdx3) + abs(mdy3) >= self.max_distance / 0.7:
                        self.bad_packets.add(packet['time'])
                        time_cooldown = time.time() + 2
                        if cfg.sound_effects:
                            self.play_audio(self.disrupt_sound)
                        self.thread_com['finished'] = True
                        latest_location = None
                        latest_location2 = None
                        latest_location3 = None
                        with open(self.b_binary_data_path, 'ab') as file:
                            self.write_chunk(file, dill.dumps(packet['time'], protocol=5))
                        return
            if time.time() >= time_cooldown and cfg.enable_macro_intervene and cfg.enable_super_macro:
                if latest_location is None: self.intervene_disrupt = time.time() + 0.7
                replaying_packets = True
                self.intervene_glow()
                self.thread_com[packet['time']] = True
                e = time.time() + 1
                while not all(self.thread_com.values()) and time.time() <= e and time.time() >= time_cooldown and not repeat_memory:
                    time.sleep(0.001)
                while self.action_cooldown >= time.time():
                    time.sleep(0.001)
                location2 = None
                match packet['press']:
                    case 'm':
                        dx = packet['flocation'][0] - packet['flocation2'][0]
                        dy = packet['flocation'][1] - packet['flocation2'][1]
                        if abs(dx) + abs(dy) >= self.max_distance / 1.3 or packet['duration'] > 1:
                            location2 = (int((packet['flocation2'][0] / self.monitor_x) * window_dimensions[0] + window_position[0]), int((packet['flocation2'][1] / self.monitor_y) * window_dimensions[1] + window_position[1]))
                            zhmiscellany.misc.click_pixel(location, **self.click_args.get(packet['mouse_button'], {}), act_start=True, act_end=False, click_duration=0.01)
                            if cfg.sound_effects:
                                self.play_audio(self.mouse_sound)
                            zhmiscellany.misc.click_pixel(location2, **self.click_args.get(packet['mouse_button'], {}), act_start=False, act_end=False, animation_time=0.1, animation_easing=True)
                            zhmiscellany.misc.click_pixel(location2, **self.click_args.get(packet['mouse_button'], {}), act_start=False, act_end=True, click_duration=0.01)
                        else:
                            if latest_location is None:
                                zhmiscellany.misc.click_pixel(location, **self.click_args.get(packet['mouse_button'], {}), act_start=False, act_end=False, animation_time=0.05, animation_easing=True)
                            zhmiscellany.misc.click_pixel(location, **self.click_args.get(packet['mouse_button'], {}), click_duration=self.actions_per_second)
                            if cfg.sound_effects:
                                self.play_audio(self.mouse_sound)
                    case 'k':
                        zhmiscellany.misc.click_pixel(location, act_start=False, act_end=False, click_end_duration=packet['duration'])
                        zhmiscellany.macro.press_key(packet['keys_held'][0], act_end=False)
                        if cfg.sound_effects:
                            self.play_audio(self.keyboard_sound)
                        zhmiscellany.macro.press_key(packet['keys_held'][0], act_start=False)
                    case 's':
                        zhmiscellany.misc.click_pixel(location, act_start=False, act_end=False, click_end_duration=extra_hold_time / 2)
                        if cfg.sound_effects:
                            self.play_audio(self.scroll_sound)
                        zhmiscellany.misc.scroll(packet['direction'])
                if cfg.return_cursor: zhmiscellany.misc.click_pixel(x, y, act_start=False, act_end=False)
                latest_location = location
                latest_location3 = (x, y)
                if location2 is None:
                    latest_location2 = location
                else:
                    latest_location2 = location2
                self.action_cooldown = time.time() + 0.05
                if not repeat_memory:
                    self.thread_com['save_packet'] = True
                    self.thread_com['finished'] = True
                    return
            else:
                self.thread_com['done'] = True
                return

    def write_chunk(self, file, chunk):
        file.write(struct.pack('<I', len(chunk)))
        file.write(chunk)

    def delete_recent_memory(self, ct=180):
        global latest_location, latest_location2, latest_location3
        print('delete recent memory')
        if cfg.sound_effects:
            self.play_audio(self.disrupt_sound)
        current = time.time() + 0.1
        old_time = current - ct
        for i in reversed(self.packets):
            ptime = i['time']
            if old_time <= ptime:
                self.bad_packets.add(ptime)
            else:
                break
        latest_location = None
        latest_location2 = None
        latest_location3 = None
        # for i in reversed(self.frames):
        #     ptime = i['time']
        #     if old_time <= ptime:
        #         self.bad_packets.add(ptime)

    def delete_all_memory(self):
        global latest_location, latest_location2, latest_location3
        self.packets = []
        self.bad_packets = set()
        self.frames = []
        self.frame_hashes = {}
        print('delete all')
        if cfg.sound_effects:
            self.play_audio(self.disrupt_sound)
        for name in os.listdir(self.macro_memory_folder):
            full_path = os.path.join(self.macro_memory_folder, name)
            if name not in {'.gitignore', 'compressed'}:
                if os.path.isdir(full_path):
                    shutil.rmtree(full_path)
                else:
                    os.remove(full_path)
        latest_location = None
        latest_location2 = None
        latest_location3 = None

        for name in os.listdir(self.compression_folder):
            full_path = os.path.join(self.compression_folder, name)
            if os.path.isdir(full_path):
                shutil.rmtree(full_path)
            else:
                os.remove(full_path)

    def compressor(self):
        time.sleep(1)

        def get_file_number():
            files = zhmiscellany.fileio.abs_listdir(self.compression_folder)
            if files:
                files = [os.path.basename(file) for file in files if os.path.isfile(file)]
                numbers = [int(file.split('_')[0]) for file in files]
                return max(numbers) + 1
            else:
                return 0

        def get_folder_size(path):
            return sum(  # DNO
                os.path.getsize(os.path.join(dirpath, f))  # DNO
                for dirpath, _, filenames in os.walk(path)
                for f in filenames
            )  # DNO

        zhmiscellany.fileio.create_folder(self.compression_folder)
        while True:
            try:
                if os.path.exists(self.p_binary_data_path):
                    if os.path.getsize(self.p_binary_data_path) > 8388608:
                        with open(self.p_binary_data_path, 'rb') as f:
                            data = f.read()
                        with open(self.p_binary_data_path, 'wb') as f:
                            f.write(b'')
                        data = zlib.compress(data)
                        file = f'{get_file_number()}_p_compressed'
                        with open(os.path.join(self.compression_folder, file), 'wb') as f:
                            f.write(data)
                if os.path.exists(self.f_binary_data_path):
                    if os.path.getsize(self.f_binary_data_path) > 8388608:
                        with open(self.f_binary_data_path, 'rb') as f:
                            data = f.read()
                        with open(self.f_binary_data_path, 'wb') as f:
                            f.write(b'')
                        data = zlib.compress(data)
                        file = f'{get_file_number()}_f_compressed'
                        with open(os.path.join(self.compression_folder, file), 'wb') as f:
                            f.write(data)
                if os.path.exists(self.b_binary_data_path):
                    if os.path.getsize(self.b_binary_data_path) > 8388608:
                        with open(self.b_binary_data_path, 'rb') as f:
                            data = f.read()
                        with open(self.b_binary_data_path, 'wb') as f:
                            f.write(b'')
                        data = zlib.compress(data)
                        file = f'{get_file_number()}_b_compressed'
                        with open(os.path.join(self.compression_folder, file), 'wb') as f:
                            f.write(data)
                if os.path.exists(self.h_binary_data_path):
                    if os.path.getsize(self.h_binary_data_path) > 8388608:
                        with open(self.h_binary_data_path, 'rb') as f:
                            data = f.read()
                        with open(self.h_binary_data_path, 'wb') as f:
                            f.write(b'')
                        data = zlib.compress(data)
                        file = f'{get_file_number()}_h_compressed'
                        with open(os.path.join(self.compression_folder, file), 'wb') as f:
                            f.write(data)
                if get_folder_size(self.macro_memory_folder) > cfg.max_memory_size * 1024 * 1024:
                    median_p_signi = 0.3
                    median_f_signi = 0.3

                    signi_values = sorted(i['signi'] for i in self.packets if 'signi' in i)
                    n = len(signi_values)
                    if n:
                        mid = n // 2
                        lower_half = signi_values[:mid] if n % 2 == 0 else signi_values[:mid]
                        m = len(lower_half)
                        if m:
                            q1_mid = m // 2
                            if m % 2 == 0:
                                median_p_signi = (lower_half[q1_mid - 1] + lower_half[q1_mid]) / 2
                            else:
                                median_p_signi = lower_half[q1_mid]

                    signi_values = sorted(i['signi'] for i in self.frames if 'signi' in i)
                    n = len(signi_values)
                    if n:
                        mid = n // 2
                        lower_half = signi_values[:mid] if n % 2 == 0 else signi_values[:mid]
                        m = len(lower_half)
                        if m:
                            q1_mid = m // 2
                            if m % 2 == 0:
                                median_f_signi = (lower_half[q1_mid - 1] + lower_half[q1_mid]) / 2
                            else:
                                median_f_signi = lower_half[q1_mid]

                    new_p = [k for k in self.packets if k['signi'] > median_p_signi and k['time'] not in self.bad_packets]
                    new_f = [f for f in self.frames if f['signi'] > median_f_signi]
                    all_hashes = {i['hash'] for i in new_f}
                    new_h = {h: self.frame_hashes[h] for h in all_hashes if h in self.frame_hashes}

                    for name in os.listdir(self.macro_memory_folder):
                        full_path = os.path.join(self.macro_memory_folder, name)
                        if name not in {'.gitignore', 'compressed'}:
                            if os.path.isdir(full_path):
                                shutil.rmtree(full_path)
                            else:
                                os.remove(full_path)

                    for name in os.listdir(self.compression_folder):
                        full_path = os.path.join(self.compression_folder, name)
                        if os.path.isdir(full_path):
                            shutil.rmtree(full_path)
                        else:
                            os.remove(full_path)
                    for i in new_p:
                        with open(self.p_binary_data_path, 'ab') as file:
                            self.write_chunk(file, dill.dumps(i, protocol=5))
                    for i in new_f:
                        with open(self.f_binary_data_path, 'ab') as file:
                            self.write_chunk(file, dill.dumps(i, protocol=5))
                    with open(self.h_binary_data_path, 'ab') as file:
                        self.write_chunk(file, dill.dumps(new_h, protocol=5))
                    self.packets = new_p
                    self.frames = new_f
                    self.frame_hashes = new_h
                    self.bad_packets = set()
                    continue
            except:
                pass
            time.sleep(3)