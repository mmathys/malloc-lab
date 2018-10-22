/*
 * this is a explicit list implementation
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define DEBUG 0

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE sizeof(void *)
#define DSIZE (2 * WSIZE)
#define CHUNKSIZE (1 << 12)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp)-WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(((void *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((void *)(bp)-GET_SIZE(((void *)(bp)-DSIZE)))

/* Given block ptr bp, compute address of next or prev free */
#define NEXT_FREE_BLKP(bp) (*(char **)(bp))
#define PREV_FREE_BLKP(bp) (*(char **)(bp + WSIZE))

/* set next and prev pointers to null */
#define INIT_NEXT_FREE_BLKP(bp) (*((char **)(bp)) = NULL)
#define INIT_PREV_FREE_BLKP(bp) (*(char **)(bp + WSIZE) = NULL)

/* set next and prev pointers to something */
#define SET_NEXT_FREE_BLKP(bp, next) (*((char **)(bp)) = next)
#define SET_PREV_FREE_BLKP(bp, prev) (*(char **)(bp + WSIZE) = prev)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *heap_listp;
static void *free_listp;
static void add_free_pointers(void *bp);
static void remove_free_pointers(void *bp);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_free_pointers(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    free_listp = NULL;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * helper functions
 */

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    { /* Case 1 */
        add_free_pointers(bp);
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_free_pointers(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        add_free_pointers(bp);
    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_free_pointers(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        add_free_pointers(bp);
    }

    else if (!prev_alloc && !next_alloc)
    { /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_free_pointers(PREV_BLKP(bp));
        remove_free_pointers(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0)); // BUG WAS HERE!
        PUT(FTRP(bp), PACK(size, 0));
        add_free_pointers(bp);
    }
    else
    {
        printf("error undefined behavior\n");
        exit(1);
    }
    return bp;
}

static void add_free_pointers(void *bp)
{
    if (DEBUG)
    {

        size_t size = GET_SIZE(HDRP(bp));
        if (size < 4 * WSIZE)
        {
            printf("error: cannot set free pointers for a block of length %lu words!\n", size / WSIZE);
            exit(1);
        }
    }

    // first block, intialize free block pointers with null pointers!
    if (free_listp == NULL)
    {

        if (DEBUG)
        {
            printf("insert first free block %p\n", bp);
        }

        free_listp = bp;
        INIT_NEXT_FREE_BLKP(bp); // set next pointer to null
        INIT_PREV_FREE_BLKP(bp); // set prev pointer to null

        if (DEBUG)
        {
            if (PREV_FREE_BLKP(bp) != NULL || NEXT_FREE_BLKP(bp) != NULL)
            {
                printf("error: could not initialize next pointers.\n");
                exit(1);
            }
        }
        return;
    }

    /* FASTER but less efficient? */
    INIT_PREV_FREE_BLKP(bp);
    SET_NEXT_FREE_BLKP(bp, free_listp);
    SET_PREV_FREE_BLKP(free_listp, bp);
    free_listp = bp;

    /* alternative algo for sorting by addresses - slow.
    void *prev = (void *)free_listp;
    void *next = (void *)NEXT_FREE_BLKP(prev); // can be null

    if (prev == bp)
    {
        printf("conflict. prev = bp\n");
        exit(1);
    }

    while (next != NULL && next < bp)
    {
        prev = next;
        next = NEXT_FREE_BLKP(next);
    }

#ifdef DEBUG
    printf("insert fit: %p / %p / %p\n", prev, bp, next);
#endif

    if (bp < prev)
    {
#ifdef DEBUG
        printf("inserting %p before %p\n", bp, prev);
#endif
        free_listp = bp;
        INIT_PREV_FREE_BLKP(bp);
        SET_NEXT_FREE_BLKP(bp, prev);
        SET_PREV_FREE_BLKP(prev, bp);
    }
    else
    {
#ifdef DEBUG
        printf("inserting %p before %p and after %p\n", bp, prev, next);
#endif
        SET_NEXT_FREE_BLKP(prev, bp);
        SET_PREV_FREE_BLKP(bp, prev);
        if (next != NULL)
        {
            SET_NEXT_FREE_BLKP(bp, next);
            SET_PREV_FREE_BLKP(next, bp);
        }
        else
        {
            INIT_NEXT_FREE_BLKP(bp);
        }
    }
    */
}

/**
 * Removes the free pointers so that the prev and next blocks skip the block in question
 */
static void remove_free_pointers(void *bp)
{
    if (DEBUG)
    {
        size_t size = GET_SIZE(HDRP(bp));
        if (size < 4 * WSIZE)
        {
            printf("error: cannot remove free pointers for a block of length %lu words!\n", size);
            exit(1);
        }
    }
    void *prev = PREV_FREE_BLKP(bp);
    void *next = NEXT_FREE_BLKP(bp);

    if (DEBUG)
        printf("deleting %p / %p / %p\n", prev, bp, next);

    if (prev != NULL && next != NULL)
    {
        if (DEBUG)
            printf("deleting free block %p between %p and %p\n", bp, prev, next);
        SET_NEXT_FREE_BLKP(prev, next);
        SET_PREV_FREE_BLKP(next, prev);
    }
    else if (prev != NULL && next == NULL)
    {
        if (DEBUG)
            printf("deleting next pointer of prev (%p)\n", prev);
        INIT_NEXT_FREE_BLKP(prev);
    }
    else if (prev == NULL && next != NULL)
    {
        if (DEBUG)
            printf("deleting first block %p, setting head to %p!\n", bp, next);
        INIT_PREV_FREE_BLKP(next);
        free_listp = next;
    }
    else if (prev == NULL && next == NULL)
    {
        if (DEBUG)
            printf("deleting only free block %p\n", bp);
        free_listp = NULL;
    }
}

static void *find_fit(size_t asize)
{
    /* First fit search */
    void *bp;

    if (free_listp == NULL)
    {
        return NULL;
    }

    if (!GET_ALLOC(HDRP(free_listp)) && (asize <= GET_SIZE(HDRP(free_listp))))
    {
        return free_listp;
    }

    for (bp = free_listp; NEXT_FREE_BLKP(bp) != NULL; bp = NEXT_FREE_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }

    return NULL; /* No fit */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) // >= 4 words
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_free_pointers(bp);

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        add_free_pointers(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_free_pointers(bp);
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (DEBUG)
        printf("Realloc: %p %lu\n", ptr, size);

    size_t original = GET_SIZE(HDRP(ptr)); // with overhead
    size_t wanted = size + 2 * WSIZE;

    if (wanted <= original)
    {
        return ptr;
    }

    /* shrinking algo - not working. maybe missing aligned size of remaining
    if (wanted <= original - 4 * WSIZE)
    {
        // shrink
        // make block smaller
        size_t newsize = size + 2 * WSIZE;
        size_t remaining = original - newsize;
        PUT(HDRP(ptr), PACK(newsize, 1));
        PUT(FTRP(ptr), PACK(newsize, 1));

        void *next = NEXT_BLKP(ptr);
        PUT(HDRP(next), PACK(remaining, 0));
        PUT(FTRP(next), PACK(remaining, 0));
        coalesce(next);

        return ptr;
    }*/

    if (wanted > original)
    {
        void *next = NEXT_BLKP(ptr);
        size_t alloc = GET_ALLOC(HDRP(next));
        size_t nextSize = GET_SIZE(HDRP(next));

        if (!alloc && original + nextSize >= wanted)
        {
            remove_free_pointers(next);
            PUT(HDRP(ptr), PACK(original + nextSize, 1));
            PUT(FTRP(ptr), PACK(original + nextSize, 1));
            return ptr;
        }
    }

    // backup strategy with copying.
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((void *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
