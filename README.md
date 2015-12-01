# The HashSieve algorithm



Included in this repository is a proof-of-concept implementation of the HashSieve algorithm for solving the shortest vector problem (SVP) on lattices, introduced in the paper:

 

 - Thijs Laarhoven, **Sieving for shortest vectors in lattices using angular locality-sensitive hashing**, *Proceedings of CRYPTO'15*.



This code is released under the MIT license: you can basically do anything you want with/to the code, as long as you give proper attribution back to me, and as long as you do not hold me responsible for anything that happens to your machine as a result of running this code. So if the source code includes a virus which allows me to take over your computer, that's your own fault.



There is only one source file, called `hashsieve.cpp`, which is set to verbose mode, outputting new records each time it finds a new shortest vector in the input lattice. The input filename is assumed to follow the format "dim40sd0.txt", as is also the case for the [SVP challenge]  but this format can be adjusted at the beginning of the main algorithm loop. The algorithm further keeps track of various statistics, which are stored in the file `hashsieve-results.txt`.



For any further questions or comments, feel free to contact me at mail@thijs.com.



[//]: # (These are reference links used in the body of this note and get stripped out when the markdown processor does its job. There is no need to format nicely because it shouldn't be seen. Thanks SO - http://stackoverflow.com/questions/4823468/store-comments-in-markdown-syntax)

   

  [SVP challenge]: http://latticechallenge.org/svp-challenge/index.php


