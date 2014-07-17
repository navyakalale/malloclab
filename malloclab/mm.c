/*
 * mm.c
 * niloyg - Niloy Gupta
 * email- niloyg@andrew.cmu.edu
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a full description of your solution.
 */


#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif
/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  1<<12  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst
#define MINIMUM    24  /* minimum block size */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

#define GETP(p)       ((void *)(p))            //line:vm:mm:get
#define PUTP(p, val)  (*(void *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp
/*#define NEXT_FREE(bp) (*(char **)(bp))
#define PREV_FREE(bp) (*((char **)(bp) + DSIZE))*/

#define PREV_FREE(bp) (*(char **)(bp))
#define NEXT_FREE(bp) (*((char **)(bp) + 1))
/* Given block ptr bp, compute address of next and previous blocks */
/*#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp
*/
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))
/* $end mallocmacros */


//static char *rover;
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void insert_free_list(void *bp);
static void remove_block(void *bp);




static char *heap_listp = 0;
static char *heap_header = 0;
static char *free_listp = 0;
//static int malloc_count = 0;
//static int free_count = 0;

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {


		if ((heap_listp = mem_sbrk(2*MINIMUM)) == NULL)
			return -1;

		PUT(heap_listp, 0); //Alignment padding

		/*initialize dummy block header*/
		PUT(heap_listp + WSIZE, PACK(MINIMUM, 1)); //WSIZE = padding
		PUT(heap_listp + DSIZE, 0); //NEXT pointer
		PUT(heap_listp + DSIZE+WSIZE, 0); //PREV pointer

		/*initialize dummy block footer*/
		PUT(heap_listp + MINIMUM, PACK(MINIMUM, 1));

		/*initialize epilogue*/
		PUT(heap_listp+WSIZE + MINIMUM, PACK(0, 1));
		//PUT(heap_listp+ (2*MINIMUM), PACK(0, 1));

		/*initialize the free list pointer to the tail block*/
		free_listp = heap_listp + DSIZE;
		heap_listp += DSIZE  ;
		heap_header = heap_listp;


		/*return -1 if unable to get heap space*/
		if ((heap_listp=extend_heap(CHUNKSIZE/WSIZE)) == NULL)
			return -1;
		//heap_listp = free_listp;
		return 0;

}

static void *extend_heap(size_t words)
{
	char *bp;
		size_t size;

		/* Allocate an even number of words to maintain alignment */
		size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
		if (size < MINIMUM)
			size = MINIMUM;
		if ((long)(bp = mem_sbrk(size)) == -1)
			return NULL;

		/* Initialize free block header/footer and the epilogue header */
		PUT(HDRP(bp), PACK(size, 0));         /* free block header */
		PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
		PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

		/* Coalesce if the previous block was free and add the block to
		 * the free list */
		//mm_checkheap(1);
		return coalesce(bp);                                //line:vm:mm:returnblock

}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || (PREV_BLKP(bp) == bp);
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1 */
    if (prev_alloc && next_alloc)
    {

    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	remove_block(NEXT_BLKP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));

    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	bp = PREV_BLKP(bp);
	remove_block(bp);
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));


    }

    else {                                     /* Case 4 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
	    GET_SIZE(HDRP(NEXT_BLKP(bp)));
	void *pbp = PREV_BLKP(bp);
	remove_block(pbp);
	void *nbp = NEXT_BLKP(bp);
	remove_block(nbp);
	bp = PREV_BLKP(bp);
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));


    }
/* $end mmfree */

/* $begin mmfree */
    insert_free_list(bp);
    return bp;
}

static void insert_free_list(void *bp)
{
	NEXT_FREE(bp) = free_listp;
	PREV_FREE(free_listp) = bp;
	PREV_FREE(bp) = NULL;
	free_listp = bp;
	/*int **c_bp = (int **)bp;
	c_bp[0] = (int *)free_listp;
	*(free_listp +8) = (char *)c_bp;
	c_bp[1] = NULL;
	free_listp = bp;*/
}

static void remove_block(void *bp)
{
	if (PREV_FREE(bp) != NULL )
		NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
	else
			free_listp = NEXT_FREE(bp);
	PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
	/*int **c_bp = (int **)bp;
	int *bp_prev = c_bp[1];
	int *bp_next = c_bp[0];
	if (c_bp[1] != NULL )
		bp_prev[0] = c_bp[0];
		else
				free_listp = (char *)c_bp[0];
		bp_next[1] = c_bp[1];*/
}
/*
 * malloc
 */
void *malloc (size_t size)
{
	//printf("\nMalloc Count: %d\n",++malloc_count);
	size_t asize;      /* adjusted block size */
	size_t extendsize; /* amount to extend heap if no fit */
	char *bp;

	/* Ignore spurious requests */
	if (size <= 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs */
	asize = MAX(ALIGN(size) + DSIZE, MINIMUM);

	/* Search the free list for a fit */
	if ((bp = find_fit(asize)))
	{
		place(bp, asize);
		//mm_checkheap(1);
		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);
	//return NULL if unable to get heap space
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	place(bp, asize);
	//mm_checkheap(1);
	return bp;

}

/*
 * free
 */
void free (void *ptr) {

	//printf("\nFree Count: %d\n",++free_count);

	/* $end mmfree */
	    if(ptr == 0)
		return;

	/* $begin mmfree */
	    size_t size = GET_SIZE(HDRP(ptr));
	/* $end mmfree */
	    if (heap_listp == 0){
		mm_init();
	    }
	/* $begin mmfree */

	    PUT(HDRP(ptr), PACK(size, 0));
	    //NEXT_FREE(ptr) = NULL;
	    //PREV_FREE(ptr) = NULL;
	    PUT(FTRP(ptr), PACK(size, 0));
	    coalesce(ptr);
	    //mm_checkheap(1);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
	free(oldptr);
	return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
	return malloc(size);
    }
    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
	return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size)
{
	size_t bytes = nmemb * size;
	  void *newptr;

	  newptr = malloc(bytes);
	  memset(newptr, 0, bytes);

	  return newptr;
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
     /* $end mmplace-proto */
{
	void *next_bp;
    size_t csize = GET_SIZE(HDRP(bp));

  /*  if ((csize - asize) >= (2*DSIZE)) {
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }*/

	//char *next_free_ptr = NEXT_FREE(bp);
	//char *prev_free_ptr = PREV_FREE(bp);

    if ((csize - asize) >= MINIMUM)
	{
    	PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		remove_block(bp);
		next_bp = NEXT_BLKP(bp);
		PUT(HDRP(next_bp), PACK(csize-asize, 0));
		PUT(FTRP(next_bp), PACK(csize-asize, 0));
		coalesce(next_bp);
	}
	else
	{
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		remove_block(bp);
	}
    /*Empty next and prev for allocated block*/
   // next_free_ptr = NULL;
    //prev_free_ptr = NULL;
}
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
/* $end mmfirstfit */
    /* Next fit search */
    char *bp;

    /* Search from the rover to the end of list */
  /*  for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;*/
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE(bp))
    	{
    		if (asize <= (size_t)GET_SIZE(HDRP(bp)))
    			return bp;
        	}
    	return NULL; // No fit


    /* search from start of list to old rover */
    /*for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;*/
    /*for (rover = heap_listp; rover < oldrover; rover = NEXT_FREE(rover))
    	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
    	    return rover;*/

    return NULL;  /* no fit found */


}

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

   /* printf("%p: header: [%d:%c] nextFree: %p prevFree: %p footer: [%d:%c]\n", bp,
	(int)hsize, ((int)halloc ? 'a' : 'f'),
	NEXT_FREE(bp)!=NULL?NEXT_FREE(bp):0,PREV_FREE(bp)!=NULL?PREV_FREE(bp):0,
	(int)fsize, ((int)falloc ? 'a' : 'f'));*/

	if (halloc)
		printf("%p: header:[%d:%c] footer:[%d:%c]\n", bp,
			(int)hsize, (halloc ? 'a' : 'f'),
			(int)fsize, (falloc ? 'a' : 'f'));
	else
		printf("%p:header:[%d:%c] prev:%p next:%p footer:[%d:%c]\n",
			bp, (int)hsize, (halloc ? 'a' : 'f'), PREV_FREE(bp),
			NEXT_FREE(bp), (int)fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}

/*
 * checkheap - Minimal check of the heap for consistency
 */

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose)
{

    char *bp = heap_listp;

    if (verbose)
    {
	printf("Heap (%p):\n", heap_listp);
    printf("Free List (%p):\n", free_listp);
    }

    if ((GET_SIZE(HDRP(heap_header)) != MINIMUM) || !GET_ALLOC(HDRP(heap_header)))
    {
	//printf("Bad prologue header\n");
	//return 1;
    }
    checkblock(heap_listp);
    for (bp = heap_listp;GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose)
	    printblock(bp);
	checkblock(bp);
    }
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    {
    	printf("Bad epilogue header\n");
    	//return 1;
    }

    return 0;
}
