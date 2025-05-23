# this is the Super Macro showcased in my video. 
## The Super Macro is an A.I. powered macro, which listens to tasks recorded and intervenes for itself when it feels necessary. I'm just posting this here for nerds who wanna see how it works and that it's not a virus. To actually use the Super Macro, it's available on Zelesis: https://zelesis.com/

### the video does a very bad job at explaining how this works for the sake of retaining simplicity in the video, so i'll explain it a little more here.

1.  Screenshots are nearly always being captured withing the `screenshot_loop function`, which saves the screenshots in a hashing system for easy lookup and storage concerns.
   it only saves to file if listening is activeling on or the user is allowing the macro to intervene.
2. All actions are recorded and saved as self.packets. Each packet is saved with the 'location' it occured at, which gets converted into `flocation` using the focused windows position and dimensions.
   `flocation` can easily be imagined as what the location would be if the application you were on was full screen, and you clicked at the same relative point.
    Each packet also comes with an `area` value, which is a cropped screenshot of where you clicked. These screenshots are created by taking a recent frame, moving the inputed x and y where the action occured to a more saturated area to help with small miss clicks,
   then sending 4 detection lines out from the new center x, y. These lines will stop when they run into a pixel that has a harsh color change. This neatly crops the screenshot. But those are still shit, because often times there is a better, slightly older, screenshot available.
   So it does this process again and compares the first and second screenshot, and if they're similar enough it'll chose the older screenshot. And repeat this process again till it's no longer similar or too old. Then it returns the final cropped screenshot as the `area` inside the packet.
   Each packet also has a signi (significance) score, which helps summerize how useful that packet likely is when replaying later. This is done by taking the max of (matching the flocation's distance to all the other flocations) and (the probability that packets array will show up).
3. If intervening is turned on, the macro will try comparing all the screenshots captured with the most recent. This is done more effictevely by generating a mask based on similarities between one other that has a high similarity. Once it gets all the screenshots
   with a high similarity, it bisects all the packets that happened at the time of those screenshots. Then gathers all the ones around those that had a high signi (significance) score. Then with the new group of packets it removes the duplicates by comparing the rgb histogram of each one.
   Then sorts the packets remaining based on the possible order the origionally may've been captured from. This is done by finding the absolute difference between each packet and the starting packet of its group, and aranging them from there.
   And after grouping packets that occured at the same time, it's time to replay them. It goes through and sends each packet/packets (if grouped) to `replay_actions`.
4. There's also a `quick_intervene`, which gets called when ever you do a click. This checks if all you past clicks you've done had similar 'areas' (arrays). If it comes out true, then it'll replay the most recent click using 'replay_actions' makred as a repeating memory.
5. Replay actions takes any packet inputed, and creates a mask for where it's likely to appear on the screen based on prior events. Using this mask, we can take another screenshot of the current screen, and crop it to where the higher values are on the mask. This limits the search area nad helps speed up the macro's preformance.
   Then given this area, we take the packet's `area` and use `cv2.matchTemplate` to locate where it could be found on the screen. We take the top 10 results and copare them to where they line of on the mask. by taking the minimum values for the confidence that it's there,
   and the likelyhood of it being there (decided by the mask), we have a list of secure spots it could be. And if the top one is above a threshold, we would want to replay it. Before replaying there's some checks that need to be done.
   First, we take the prominenet color of the packets array, and try gently moving the discovered x, y slightly closer to where that is on the screen (for more accurate clicks). Secondly, and this sound counterintuitive, we'd actually want to randomize the location decided a little
   if the last action done was also around there (this could be because the first time it missed). Then when replaying it just sees what packet it is and executes that action using `zhmiscellany`. For clicks, this is also where drags are checked. if the duration of the click is past a second
   and the start x, y is far enough from the end x, y, it's considered a dragging motion and is replayed like one.
6. compressing compresses the files. hjfkdhjklsdffdskhjlfdskhjiulfdshjikofdshjklafshjdklhjkfldsa
7. if the size of the memory folder is large enough, it purges a lot of the memories below the signi's quartile 1.
8. the glowing uses pyqt
9. fuck i'm tired
