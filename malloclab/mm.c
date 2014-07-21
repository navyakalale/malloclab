/*
 * mm.c
 * niloyg - Niloy Gupta
 * email- niloyg@andrew.cmu.edu
 *
 *
 * This submission for the malloc lab checkpoint uses an explicit list implementation
 * with a first fir strategy.
 *
 * A free block has the following structure
 * Header(4 bytes)|Next PTR(8 bytes)| PREV PTR(8 bytes)|Footer(4 bytes)
 *
 * An allocated block has the following structure
 * Header(4 bytes)|Payload (size)|Footer(4 bytes)
 *
 * When malloc is called, it returns the allocated amount of memory.
 * If it runs out of memeory blocks, it more from sbrk.
 *
 * The free block provided by malloc is fetched from the free list aka
 * a bi-directinal linkedlist of pointers to free blocks
 *
 * When a block is freed by calling free, it is coalesced i.e. merged with adjoining free blocks
 * if any and inserted at the head of the free list.
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

#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  1<<9  /* Extend heap by this amount (bytes) */
#define HEADER_SIZE    24  /* minimum block size */
#define LIST_NO 20



/* 4 or 8 byte alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define GETP(p)       ((void *)(p))
#define PUTP(p, val)  (*(void *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* The pointer to the next free block is stored in the current pointer bp
 * The pointer to the previous free block is stored one address space away.
 */
#define NEXT_FREE_BLK(bp) (*(char **)(bp))
#define PREV_FREE_BLK(bp) (*((char **)(bp) + 1))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static void *extend_heap(size_t words);
static void alloc(void *free_block, size_t req_size);
static void *first_fit(size_t req_size);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void insert_free_list(void *bp, int size);
static void remove_block(void *bp,int size);
static int get_free_list_head( unsigned int n);



static char *heap_list_head = 0;
static char *heap_header = 0;
static char *free_list_head[LIST_NO];
//static int malloc_count = 0; /*DEbugging variables*/
//static int free_count = 0;

/* init_fee_list- Sets the pointers pointing to heads of free lists to 0
 *
 */
void init_free_list(char *bp)
{
	for(int i=0;i<LIST_NO;i++)
		free_list_head[i] = bp;
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void)
{

	if ((heap_list_head = mem_sbrk(2 * HEADER_SIZE)) == NULL )
		return -1;

	PUT(heap_list_head, 0); //Alignment padding

	/*initialize dummy block header*/
	PUT(heap_list_head + WSIZE, PACK(HEADER_SIZE, 1)); //WSIZE = padding
	PUT(heap_list_head + DSIZE, 0); //pointer to next free block
	PUT(heap_list_head + DSIZE+WSIZE, 0); //pointer to the previous free block

	/*initialize dummy block footer*/
	PUT(heap_list_head + HEADER_SIZE, PACK(HEADER_SIZE, 1));

	/*initialize epilogue*/
	PUT(heap_list_head+WSIZE + HEADER_SIZE, PACK(0, 1));


	/*initialize the free list pointer to the tail block*/

	heap_list_head += DSIZE;
	heap_header = heap_list_head;
	init_free_list(heap_list_head);

	/*return -1 if unable to get heap space*/
	if ((heap_list_head = extend_heap(CHUNKSIZE / WSIZE)) == NULL )
		return -1;
	return 0;

}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if (size < HEADER_SIZE)
		size = HEADER_SIZE;
	if ((long) (bp = mem_sbrk(size)) == -1)
		return NULL ;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

	/* Coalesce if the previous block was free and add the block to
	 * the free list */
	//mm_checkheap(1);
	return coalesce(bp);                                //line:vm:mm:returnblock

}

/* coalesce - Merge the free block neighbours and place them
 * at the head of the free list
 *
 */

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || (PREV_BLKP(bp) == bp);
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc)
	{
		// Do nothing
	}

	else if (prev_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		remove_block(NEXT_BLKP(bp),GET_SIZE(HDRP(NEXT_BLKP(bp))));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
	}

	else if (!prev_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		bp = PREV_BLKP(bp);
		remove_block(bp,GET_SIZE(HDRP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

	}

	else
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
		void *pbp = PREV_BLKP(bp);
		remove_block(pbp, GET_SIZE(HDRP(pbp)));
		void *nbp = NEXT_BLKP(bp);
		remove_block(nbp, GET_SIZE(HDRP(nbp)));
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}

	insert_free_list(bp,size);
	return bp;
}

/*insert_free_list - inserts the pointer at the head of the
 * free list.
 *
 */
static void insert_free_list(void *bp, int size)
{
	int free_list_index = get_free_list_head(size);
	NEXT_FREE_BLK(bp) = free_list_head[free_list_index];
	PREV_FREE_BLK(free_list_head[free_list_index]) = bp;
	PREV_FREE_BLK(bp) = NULL;
	free_list_head[free_list_index] = bp;
}

/*remove_block - Removes the block from the free list
 * Sets the next pointer of the previous-free block of bp to the next-free block of bp
 * Sets the previous pointer of the next-free block of bp to the previous-free block of bp
 */
static void remove_block(void *bp, int size)
{
	if (PREV_FREE_BLK(bp) != NULL )
		NEXT_FREE_BLK(PREV_FREE_BLK(bp)) = NEXT_FREE_BLK(bp);
	else
	{
		int free_list_index = get_free_list_head(size);
		free_list_head[free_list_index] = NEXT_FREE_BLK(bp);
	}
	PREV_FREE_BLK(NEXT_FREE_BLK(bp)) = PREV_FREE_BLK(bp);
}
/*
 * malloc
 */
void *malloc (size_t size)
{
	//printf("\nMalloc Count: %d\n",++malloc_count);
	size_t asize;
	size_t extendsize;
	char *bp;

	/* Ignore spurious requests */
	if (size <= 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs */
	asize = MAX(ALIGN(size) + DSIZE, HEADER_SIZE);

	/* Search the free list for a fit */
	if ((bp = first_fit(asize)))
	{
		alloc(bp, asize);
		//mm_checkheap(1);
		return bp;
	}

	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL; 	//return NULL if unable to get heap space
	alloc(bp, asize);
	//mm_checkheap(1);
	return bp;

}

/*
 * free- Free the occupied block and coalesces the block
 */
void free(void *ptr)
{

	//printf("\nFree Count: %d\n",++free_count);

	if (ptr == 0)
		return;
	size_t size = GET_SIZE(HDRP(ptr));
	if (heap_list_head == 0)
		mm_init();

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);
	//mm_checkheap(1);
}

/*
 * realloc - referred mm-naive.c
 */
void *realloc(void *oldptr, size_t size)
{
	size_t oldsize;
	void *newptr;
	/* Adjust block size to include overhead and alignment reqs */
	size_t req_size = MAX(ALIGN(size) + DSIZE, HEADER_SIZE);
	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0)
	{
		free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (oldptr == NULL )
		return malloc(size);

	oldsize = GET_SIZE(HDRP(oldptr));

	if(req_size == oldsize || (oldsize-req_size)<=HEADER_SIZE)
		return oldptr;

	if(req_size <= oldsize)
	{
		PUT(HDRP(oldptr),PACK(req_size,1));
		PUT(FTRP(oldptr),PACK(req_size,1));
		PUT(HDRP(NEXT_BLKP(oldptr)),PACK(oldsize-req_size,1));
		PUT(FTRP(NEXT_BLKP(oldptr)),PACK(oldsize-req_size,1));
		free(NEXT_BLKP(oldptr));
		return oldptr;
	}

	newptr = malloc(size);
	/* If realloc() fails the original block is left untouched  */
	if (!newptr)
		return 0;

	/* Copy the old data. */

	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

	return newptr;
}

/*
 * calloc - referred mm-naive.c
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
 * alloc - Allocates  block of req_size bytes at start of free block
 *         and split if free block is larger
 */
static void alloc(void *free_block, size_t req_size)
{
	void *next_bp;
    size_t csize = GET_SIZE(HDRP(free_block));
    //Split the free block into allocated and free.
    if ((csize - req_size) >= HEADER_SIZE)
	{
    	PUT(HDRP(free_block), PACK(req_size, 1)); //Allocating the block
		PUT(FTRP(free_block), PACK(req_size, 1));
		remove_block(free_block,csize);
		next_bp = NEXT_BLKP(free_block);
		PUT(HDRP(next_bp), PACK(csize-req_size, 0));//Resetting the size of the free block
		PUT(FTRP(next_bp), PACK(csize-req_size, 0));
		coalesce(next_bp); //Coalesce of the newly resized free block
	}
	else
	{
		PUT(HDRP(free_block), PACK(csize, 1));
		PUT(FTRP(free_block), PACK(csize, 1));
		remove_block(free_block,csize);
	}

}

/*first_fit - Iterates through the free list to search for a free block
 * with size greater than or equal to the requested block size.
 *
 */
static void *first_fit(size_t req_size)
{

	char *bp;
	for (int i = get_free_list_head(req_size); i < LIST_NO; i++)
	{
		for (bp = free_list_head[i]; GET_ALLOC(HDRP(bp)) == 0; bp =NEXT_FREE_BLK(bp) )
		{
			if (req_size <= (size_t) GET_SIZE(HDRP(bp)))
				return bp;
		}
	}
	/*for (int i = 0; i < get_free_list_head(req_size); i++)
		{
			for (bp = free_list_head[i]; GET_ALLOC(HDRP(bp)) == 0; bp =NEXT_FREE_BLK(bp) )
			{
				if (req_size <= (size_t) GET_SIZE(HDRP(bp)))
					return bp;
			}
		}*/
	return NULL ; // No fit
}

static void printblock(void *bp)
{
	size_t header_size = GET_SIZE(HDRP(bp));
	size_t header_alloc = GET_ALLOC(HDRP(bp));
	size_t footer_size = GET_SIZE(FTRP(bp));
	size_t footer_alloc = GET_ALLOC(FTRP(bp));

	if (header_size == 0)
	{
		printf("%p: EOL\n", bp);
		return;
	}

	if (header_alloc)
		printf("%p: header:[%d:%c] footer:[%d:%c]\n", bp, (int) header_size,
				(header_alloc ? 'a' : 'f'), (int) footer_size, (footer_alloc ? 'a' : 'f'));
	else
		printf("%p:header:[%d:%c] prev:%p next:%p footer:[%d:%c]\n", bp,
				(int) header_size, (header_alloc ? 'a' : 'f'), PREV_FREE_BLK(bp),
				NEXT_FREE_BLK(bp), (int) footer_size, (footer_alloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
	printf("Error: %p is not 8 byte aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header and footer are not equal\n");
}

/*
 * checkheap - functions with multiple checks
 */
int mm_checkheap(int verbose)
{

	char *bp = heap_list_head;

	if (verbose)
	{
		printf("Heap (%p):\n", heap_list_head);
		//printf("Free List (%p):\n", free_list_head);
	}

	if ((GET_SIZE(HDRP(heap_header)) != HEADER_SIZE)
			|| !GET_ALLOC(HDRP(heap_header)))
	{
		//printf("Bad prologue header\n");
		//return 1;
	}
	checkblock(heap_list_head);
	for (bp = heap_list_head; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
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

static int get_free_list_head( unsigned int n)
{
	int count = 0;
	while(n>1)
	{
		n = n>>1;
		count++;
	}
	if(count > LIST_NO-1 )
		return  LIST_NO-1;
	return count;
}

