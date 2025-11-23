> {- stack --resolver lts-23.24 script
>    --package async --package binary
>    --package containers --package deepseq
>    --package directory --package mtl
>    --package stm
>    --compile
>    --ghc-options -O2 
>    --ghc-options -threaded
>    --ghc-options -rtsopts
>    --
>    +RTS -N -RTS
> -}

This post is a complete implementation of a program to find the optimal strategy for any given Yahtzee state, as described in James Glenn's 2006 paper ["An Optimal Strategy for Yahtzee"](https://www.yahtzeemanifesto.com/an-optimal-strategy-for-yahtzee.pdf).
It's written in literate Haskell, so it's been processed into an HTML file for viewing on the web, but you can download the [raw file](./ysolver.lhs) and run it using `stack ysolver.lhs` (the options at the start of the file are passed to `stack`).

I wrote it for three reasons:

1. My family plays a lot of Yahtzee and I was curious if my decision-making was anywhere near optimal.
2. I wanted to practice writing Haskell.
3. I enjoy literate programming.

Originally, I thought Haskell was a perfect choice for this problem---"this is a mildly complex math problem, Haskell is math-driven language, using Haskell should make it easy to express the math."
I quickly received a reminder that you still need to know the limitations of the computer executing your program.
Consider this program/blog post partly a record of me (re)learning these lessons the hard way and partly implementation notes for an interesting bit of math.

= Introduction

I'm not going to repeat too much of Glenn's mathematics---his paper is rather readable, and I would encourage you to read it for a full understanding of the algorithm at a conceptual level.
Instead, I will be describing the Haskell implementation in painful detail---partly because it was painful for me to write (I'm not used to trying to write performant Haskell), partly because I learned some interesting lessons along the way.
I tried my hardest to write clear and consistent code, but caveat emptor if you're looking to it as an exemplar.

First, let's talk about some high level strategy.
Glenn's algorithm is pretty simple: every state in a Yahtzee game is represented in table.
To find the ideal decision in any given state, calculate the expected score of each possible successor state; choose the decision that leads to the state with the highest expected score.
If the player isn't making a decision in the state---say, at the beginning of a turn---calculate the expected score of all possible successor states, weight them by their probabilities, and add the weighted scores together.
Store each expected score in the table and keep track of the mapping of states to tables to avoid unnecessary recalculations.

Naturally, our implementation will not be this simple.

== Imports

None of our dependencies are terribly exotic.
We'll be using standard data structures to store most of our data, though note that we're using the strict version of a `Map` to map states to expected scores.
Most of the time, Haskell's lazy nature is going to work against us.

> import Data.List (sort, foldl')
> import Data.Map.Strict (Map)
> import qualified Data.Map.Strict as Map
> import Data.Word (Word16, Word32)
> import Data.Bits

The `System` and `Data.Binary` dependencies combine to serialize data and store our table when we're done calculating it.

> import System.IO
> import System.Directory (doesFileExist)
> import Data.Binary (Binary, encode, decode, put, get, encodeFile, decodeFile)

Finally, we use various `Control` packages to handle concurrency.

> import Control.Concurrent.STM
> import Control.Concurrent
> import Control.Concurrent.Async (mapConcurrently)
> import Control.DeepSeq (force)

= Type Definitions

With the preliminaries out of the way, let's start by defining our representations of a Yahtzee game.
There is a bit of a balancing act between providing clear abstractions and maintaining performant code.

== Scorecard

Let's start with an easy one: our Yahtzee categories are defined as an `enum`, with various useful typeclasses derived for us.

> data Category = Ones | Twos | Threes | Fours | Fives | Sixes
>   | ThreeKind | FourKind | FullHouse | SmStraight | LgStraight
>   | Yahtzee | Chance
>   deriving (Eq, Ord, Show, Enum, Bounded)

The `Bounded` typeclass helps us collect all of our categories into a list.

> allCats :: [Category]
> allCats = [minBound .. maxBound]

And the `Ord` typeclass helps us tell if a category is in the upper section or not.

> isUpperCat :: Category -> Bool
> isUpperCat c = c <= Sixes

Representing a scorecard is simple because we don't need to store the scores at any given time; we just need to store whether the category is used or not.
Thirteen categories and one bit of information per category means we can fit our scorecard into a 16-bit word.

> newtype Scorecard = Scorecard Word16 deriving (Eq, Ord, Show)

No, I did not default to squeezing types into bitmaps.
Originally, I defined a scorecard far more intuitively: `newtype Scorecard = Scorecard (Map Category Bool)`.
But after completing the first version of my program, I found it to be unbearably slow---calculating even "easy" decisions (with 4--5 categories blank) took nearly an hour.
One of the bottlenecks was comparing various aspects of a state when checking if I had already calculated the expected score for a given state, including comparing different Scorecards.
(Have we already calculated the optimal decision for a state?
Well, we have to check if the state is equal to other states: does it have the same scorecard, the same dice roll, etc.)
It is unsurprisingly _much_ faster to compare two 16-bit words than to compare two full `Map` structures.

Thankfully, we can hide most of our bit flipping in the various helper functions to manipulate `Scorecard`s.
Converting from the category `enum` to the correct bit is also smoother than you might expect.

> isFull :: Scorecard -> Bool
> isFull (Scorecard w) = w == 0x1FFF  -- All 13 bits set (2^13 - 1)
>
> isUsed :: Category -> Scorecard -> Bool
> isUsed cat (Scorecard w) = testBit w (fromEnum cat)
>
> emptyCats :: Scorecard -> [Category]
> emptyCats card = [c | c <- allCats, not (isUsed c card)]
>
> fill, unfill :: Category -> Scorecard -> Scorecard
> fill cat (Scorecard w) = Scorecard (setBit w (fromEnum cat))
> unfill cat (Scorecard w) = Scorecard (clearBit w (fromEnum cat))
>
> emptycard, fullcard :: Scorecard
> emptycard = Scorecard 0
> fullcard = Scorecard 0x1FFF

== Dice Rolls

Dice rolls are represented as "multisets," or more colloquially, "bags."
A multiset is a set---in that it's unordered---but it allows multiple occurrences of the same value.
They are usually implemented as a number of keys with an occurrence count attached to each value.
A [MultiSet implementation](https://hackage.haskell.org/package/multiset-0.3.4.3/docs/Data-IntMultiSet.html) is available on Hackage, but during testing, I ran into the same problem I did with `Scorecard`s: comparing complex data structures to each other is slow.
Instead, our dice roll is similarly squeezed into a bitmap, though a multiset-inspired one.

> -- Bits 0-2: count of 1s (0-5)
> -- Bits 3-5: count of 2s (0-5)
> -- Bits 6-8: count of 3s (0-5)
> -- Bits 9-11: count of 4s (0-5)
> -- Bits 12-14: count of 5s (0-5)
> -- Bits 15-17: count of 6s (0-5)
> newtype Roll = Roll Word32 deriving (Eq, Ord, Show)
> emptyRoll :: Roll
> emptyRoll = Roll 0

![Sample dice bitmap representation](/images/dice-bitmap-transparent.svg)\

=== Manipulating Dice Rolls

However, its helper functions are significantly trickier---in part because we go out of our way to make sure they mostly reduce to flipping and shifting bits.
That means resisting the urge to build lists or other intermediate data structures.
Most of the dice roll functions are inlined due to how often we manipulate dice rolls in the course of our calculations.
I defend myself against charges of premature optimization by noting that I did profile and measure first before resorting to bitflipping.

> -- Get count of a specific die face
> occur :: Int -> Roll -> Int
> occur face (Roll w)
>   | face < 1 || face > 6 = error $ "trying to set die face out of bounds: " ++ show face

Note that here (and for the rest of this family of functions), we choose to throw an error on invalid input.
We control all calls of these functions, so any invalid input means we've made a programmers' mistake.

The basic pattern for most of these functions is extracting the three bits used to count the ocurrences of each die face and manipulating them, in the form of `(face-1) * 3`, which finds the correct bit index for a given face.

>   | otherwise = fromIntegral $ (w `shiftR` ((face - 1) * 3)) .&. 0x7
> {-# INLINE occur #-}
>
> -- Set the occurrence of a specific die face
> setOccur :: Int -> Int -> Roll -> Roll
> setOccur face count (Roll w)
>   | face < 1 || face > 6 = error $ "trying to set die face out of bounds: " ++ show face
>   | count < 0 || count > 5 = error $ "trying to set face occurs out of bounds: " ++ show count
>   | otherwise =
>       let mask = complement (0x7 `shiftL` ((face - 1) * 3))
>           cleared = w .&. mask
>           newBits = (fromIntegral count .&. 0x7) `shiftL` ((face - 1) * 3)
>        in Roll (cleared .|. newBits)
> {-# INLINE setOccur #-}

`occur` and `setOccur` are both comparatively simple.
`unionRoll`, on the other hand, is a bit messy, as what normally would have been expressed more concisely is "unrolled" for the sake of ensuring it reduces down to solely bitflipping.
An idiomatic Haskell implementation would have used some recursion and intermediate data structures.

> -- Combine two rolls (add their counts)
> -- Used for when we rolled a subset of dice and we want to combine the new roll
> -- with the saved dice.
> unionRoll :: Roll -> Roll -> Roll
> unionRoll (Roll w1) (Roll w2) = Roll $
>   let add shift = min 5 (((w1 `shiftR` shift) .&. 0x7) + ((w2 `shiftR` shift) .&. 0x7)) `shiftL` shift
>    in add 0 .|. add 3 .|. add 6 .|. add 9 .|. add 12 .|. add 15
> {-# INLINE unionRoll #-}

The rest of the dice roll functions can be written more idiomatically using the more low-level functions.

> -- Total number of dice in the roll
> rollSize :: Roll -> Int
> rollSize roll = sum [occur i roll | i <- [1..6]]
> {-# INLINE rollSize #-}
>
> -- Get list of distinct die faces present
> distinctFaces :: Roll -> [Int]
> distinctFaces roll = [i | i <- [1..6], occur i roll > 0]
> {-# INLINE distinctFaces #-}
>
> -- A roll with one die
> singletonRoll :: Int -> Roll
> singletonRoll face = setOccur face 1 emptyRoll
>
> -- Convert a list of faces into a roll
> listToRoll :: [Int] -> Roll
> listToRoll faces = foldl' unionRoll emptyRoll singles
>   where singles = map singletonRoll faces
>
> -- Convert a list of faces into a roll, checking that the roll is complete (five dice)
> listToFullRoll :: [Int] -> Roll
> listToFullRoll l
>   | length l /= 5 = error "dice rolls must be five dice"
>   | otherwise = listToRoll l

=== Dice Combinations

A large part of calculating an expected score is generating lists of possible dice combinations (and their probabilities).
These functions manipulate `Roll`s but are mostly high level enough to not need to directly flip any bits.

The problem where we have a set of $n$ elements and we want to choose $k$ elements from the set is called "n choose k" problem, or the [binomial coefficient](https://en.wikipedia.org/wiki/Binomial_coefficient).
Since we are allowed to choose combinations _with_ repetition, we use a variant---the [multiset coefficient](https://en.wikipedia.org/wiki/Multiset#Counting_multisets).
When rolling dice we have six possible faces per die ($n=6$) and $k$ is the number of dice we are rolling.

> -- Given the number of dice to roll, generate a list of all possible rolls.
> sixChooseK :: Int -> [Roll]
> sixChooseK k = map listToRoll (choose k [1..6])
>   where
>     -- choose generates the list of combinations
>     choose :: Int -> [a] -> [[a]]
>     choose 0 _  = [[]]
>     choose _ [] = []
>     choose k (x:xs)
>       | k < 0     = []
>       | otherwise = map (x:) (choose (k-1) (x:xs)) ++ (choose k xs)

Now, what are the odds of rolling a given dice roll?
This is simple to calculate: divide the [multinomial coefficient](https://en.wikipedia.org/wiki/Multinomial_theorem) by the number of outcomes per die (6) raised to the number of dice rolled.
If $k$ is the number of dice rolled, and $o_f$ is the number of occurrences for a distinct face $f$:

$$
\begin{align}
{k\choose o_6}&= \frac{k!}{\prod_{f=1}^6 o_f!} \text{ (the multinomial coefficient)} \\
\\
P\{\text{roll}\} &= \frac{k\choose o_6}{6^k}
\end{align}
$$

And in code:

> -- Given a roll, return the odds of achieving that roll
> rollOdds :: Roll -> Double
> rollOdds roll = fromIntegral multinomial / fromIntegral (6 ^ rollSize roll)
>   where
>     -- Precomputed factorials because we know n < 6
>     factorial n | n < 6 = [1, 1, 2, 6, 24, 120] !! n
>     factorial n | otherwise = error $ show n ++ "! is not precomputed"
>     occurs = map (\k -> occur k roll) (distinctFaces roll)
>     multinomial =
>       factorial (rollSize roll) `div`
>       product [factorial o | o <- occurs]

After defining the initial combination functions, we immediately go back to trying to eke out some performance wins.
We know that we'll never roll more than five dice, so we can just precompute all the possible dice combinations as well as their odds.

> -- Precompute all possible combinations of rolling any number of dice.
> -- and the odds of getting that roll.
> -- This is a total of 6 + 21 + 56 + 126 + 252 + 462 = 923 rolls
> completeRollListWithOdds :: [[(Roll, Double)]]
> completeRollListWithOdds = map collectRollOdds allRolls
>   where
>     collectRollOdds rolls = [(r, rollOdds r) | r <- rolls]
>     allRolls = map sixChooseK [1..5]
>
> -- This is just a convenient name to make future code read more nicely.
> -- Most of the time, we'll use completeRollListWithOdds !! k to get all the
> -- possible dice combinations and the odds of each from rolling k dice.
> rollFiveDice = completeRollListWithOdds !! 4

Lastly, we have all the possible combinations of rolling dice... what about the possible combinations of _keeping_ them?
We don't have any standard formulas for this, so Glenn provides the logic for finding all possible dice combinations we can keep from a given roll.

For each distinct number in our dice roll, we can choose to keep 0--n dice; i.e., if we have rolled three 2s, we can choose to keep none of them, one 2, two 2s, or all three 2s.
Then we combine each of those options with the options for all the other distinct numbers; i.e., if we have rolled two 1s to go along with our three 2s, we can keep zero 2s and zero 1s (reroll everything), or zero 2s and one 1, or zero 2s and two 1s, or one 2 and zero ones, etc., etc.

> -- Given a roll generate all the possible ways we can keep a subset of the dice
> -- excluding keeping the entire roll.
> keepCombinations :: Roll -> [Roll]
> keepCombinations roll
>   | rollSize roll == 0 = []
>   | otherwise =

Reading from in to out:
`mapM` (instead of `map`) ensures we get a list of all combinations instead of a list of length `distinctFaces`.
Then we have a list of combinations, but each combination is itself a list of rolls; we want to collapse each combination into a single roll with the fold call.
Finally, the filter excludes keeping all the dice from our list---keeping all the dice is equivalent to ending the turn and scoring the current roll in a category, which we'll handle elsewhere.

>     filter (\r -> rollSize r < rollSize roll)
>       (map (foldl unionRoll emptyRoll) $
>         mapM (decomposeFaces roll) (distinctFaces roll))
>     where
>       decomposeFaces :: Roll -> Int -> [Roll]

`decomposeFaces` provides all the options for each distinct element (zero 2s, one 2, two 2s, etc.). We represent keeping 0 with an empty roll.

>       decomposeFaces r f =
>         emptyRoll : [setOccur f i emptyRoll | i <- [1 .. occur f r]]

== Turns

Working with dice took a fair amount of time and brief foray into combinatorics.
Let's finish our representation of a Yahtzee game.

> data YTurn = YTurn { rerolls :: Int
>                    , roll :: Roll
>                    } deriving (Eq, Ord, Show)

Our types are getting simpler!
A `YTurn` is the number of rerolls we have left and the current roll.
(If the number of rerolls is 3---i.e., we're a the beginning of a turn---then the current roll is ignored.)

> isEnd :: YTurn -> Bool
> isEnd turn  = rerolls turn == 0
> isMid :: YTurn -> Bool
> isMid turn = (rerolls turn > 0) && (rerolls turn < 3)
> isBegin :: YTurn -> Bool
> isBegin turn = rerolls turn == 3
> newTurn :: YTurn
> newTurn = YTurn { rerolls = 3, roll = emptyRoll }

== Gamestates

We are almost ready to write out our complete state type.

> type UpperTotal = Int
> type YBonus = Bool

There are two stray pieces of state, besides the scorecard and the dice roll, that we care about---the current total of the upper part of our scorecard (since it affects the bonus at the end of the game) and whether the next Yahtzee earns a 100-point bonus.

> data YState = YState { card :: Scorecard
>                      , uptotal :: UpperTotal
>                      , bonus :: YBonus
>                      , turn :: YTurn
>                      } deriving (Eq, Ord, Show)
>
> newgame :: YState
> newgame = YState { card = emptycard
>                  , uptotal =  0
>                  , bonus = False
>                  , turn = newTurn }

= Solving Yahtzee

There are two parts to our algorithm for solving Yahtzee.
The first part is the actual calculations for solving any given Yahtzee state.
The second is the logic to do our calculations efficiently: threads, locks, caching, etc.
I worked hard, but did not entirely succeed, to keep the two concerns separate, so we'll have to switch back and forth between talking about program organization and our algorithm.

We'll start with the actual output of the algorithm:

> type Decision = (Double, String)

I've glued together the expected score of our game state with a prose description of the decision.
A sample output would be `(50.0, "score roll as a yahtzee")` if we're trying to decide which category to score a roll in, or `(35.2, "keep 2 1s")` if we're deciding which dice to reroll.

To store `Decision`s, we create a `Map` from `YState`s to `Decision`s.

> type DecisionMemo = TVar (Map YState (TMVar Decision))
> emptymemo :: IO DecisionMemo
> emptymemo = newTVarIO Map.empty

We label it a "memo" because it's intended to memoize solutions.
In the course of computing a solution for one state, we're going to compute solutions for lots of other states, and we don't want to compute the solution for a state more than once, so we use this structure to store all of the previously computed decisions.

For now, ignore the `TVar` and `TMVar` wrappers.
They are part of Haskell's [STM (Software Transactional Memory)](https://hackage.haskell.org/package/stm-2.5.3.1/docs/Control-Concurrent-STM.html) package and are there to make concurrency work correctly.
We'll cover how we use them in detail later.

== Computing a Score

> computeScore :: DecisionMemo -> DecisionMemo -> YState -> IO Decision

`computeScore` is the function for calculating an optimal decision from a state.
It carries around two `DecisionMemo`s---one is the _global_ memo and one is the _local_ memo.
For now, don't worry about why we have two memos---just know that memoization is happening while we look at how the calculations are working.

Let's start with the simplest scenario.
When your scorecard is full, the only thing left to score is the upper category bonus.
Remember we don't care what the _current_ score on the scorecard is, just what the future expected score is.
No decisions for the player to make here: if the upper total meets the threshold, we get the bonus.
Otherwise we get zero.

> computeScore _ _ ystate
>   | isFull (card ystate) = return $
>     if uptotal ystate >= 63
>       then (35, "end game: upper bonus achieved")
>       else (0, "end game: no upper bonus")

Our next simplest scenario is at the end of a turn: we don't need to decide how many dice to reroll or anything like that, we just need to decide which category to score our current roll in.

The math is much easier to say then to calculate: score your current roll in each category, then calculate the expected score for each of the corresponding successor states and sum them with the corresponding category score.
The category with the maximum sum is the correct decision.

> computeScore gmemo lmemo ystate
>   | isEnd (turn ystate) = do
>     let cats = emptyCats (card ystate)

Note that our threading bookkeeping is already intruding a little bit.
We use `mapConcurrently` to start the computation of each new turn in a new thread.

>     scores <- mapConcurrently (computeScoreByCategory gmemo lmemo ystate) cats
>     return $ maximum scores

Next, we handle what to do in the middle of a turn.
This is more complicated; the questions are 1) "Should we score the current roll in a category now?" and if not, 2) "How many and which dice should we reroll?"
Now the number of states starts getting larger; we have to calculate the expected scores for each category we could score the current roll in and every possible way to reroll the dice.


> computeScore gmemo lmemo ystate 
>   | isMid (turn ystate) = do

The following two lines do most of the work for this section.
`keepCombinations` generates all the ways to keep some combination of dice, and then we map our compute helper function (`computeScoreOnReroll`, in the same genre as `computeScoreByCategory`) across all combinations.

>     let keeps = keepCombinations $ roll (turn ystate)
>     scoresOnRerolls <- mapM (computeScoreOnReroll gmemo lmemo ystate) keeps

To handle the "score in a category immediately" option, we advance the state to the end of the turn, then calculate the expected score from there.
Note the call to `expectedScore` instead of `computeScore` or one of its helper functions---`expectedScore` handles all the threading and caching bookkeeping, so any time we need do that bookkeeping, we call `expectedScore` instead of `computeScore`.

>     let keepAllNextTurn = (turn ystate) { rerolls = 0 }
>         keepAllNextState = ystate { turn = keepAllNextTurn }
>     scoreOnAllKeeps <- expectedScore gmemo lmemo keepAllNextState
>     return $ maximum (scoreOnAllKeeps : scoresOnRerolls)

Finally, we handle what to do at the beginning of a turn.
This is actually simple compared to the middle of a turn---we don't have to make any decisions.
We generate all the possible rolls of five dice (and the likelihood of each roll), find the expected score of each, and weight the score by the odds of that roll occuring.

> computeScore gmemo lmemo ystate
>   | isBegin (turn ystate) =
>     let (allRolls, allRollOdds) = unzip rollFiveDice
>         nextTurns = map (YTurn ((rerolls $ turn ystate) - 1)) allRolls
>         nextStates = map (\nt -> ystate { turn = nt }) nextTurns
>      in do
>        scores <- mapM (expectedScore gmemo lmemo) nextStates
>        let weightedScores = zipWith (\(s, _) -> (s*)) scores allRollOdds
>        return $ (sum weightedScores,
>                 "expected score at turn start is " ++
>                 show (sum weightedScores))
> -- Our guards should be exhaustive; if we hit this code, we've made a mistake
> -- either in our game state or in our logic.
> computeScore _ _ ystate 
>   | otherwise = error ("shouldn't have hit this, state: " ++ show ystate)

We hid a fair amount of complexity in two helper functions: `computeScoreByCategory` and `computeScoreOnReroll`.
Both have the same logic: given a category to score in or a dice combination to keep, calculate the expected score.
`computeScore` than maps each function over every available category or every available keeps combination.
Both functions are probably more verbose than they need to be---I aimed for making it painfully clear how successor states were constructed from the initial state.

> -- Given a Yahtzee state and category to score the current roll in, calculate the
> -- expected score and return the score with a description of the category we used.
> computeScoreByCategory :: DecisionMemo -> DecisionMemo -> YState -> Category -> IO Decision
> computeScoreByCategory gmemo lmemo yst cat =
>   let (sc, ut, bo, tu) = (card yst, uptotal yst, bonus yst, turn yst)
>       dice = roll tu
>       score = scoreRollWithBonus bo dice cat
>       filledCard = fill cat sc

Note how we stop adding to the upper total once it hits 63.
This minimizes the number of states we need to store, since we only care that a state's upper categories total is 63 or above.

>       newTotal = min (ut + (if isUpperCat cat then score else 0)) 63
>       newBonus = if (cat == Yahtzee && isYahtzee dice) then True else bo
>       nextYState = YState filledCard newTotal newBonus newTurn
>    in do
>       (future, _) <- expectedScore gmemo lmemo nextYState
>       return $ (fromIntegral score + future,
>                "fill category " ++ show cat ++ ", score " ++ show score)

`computeScoreOnReroll` should look familiar, as it reuses several patterns we've already seen: getting lists of possible dice rolls and their respective probabilities, constructing successor states by mapping constructors across lists of components, mapping `expectedScore` across successor states, and then weighting the expected scores based on the odds of that state occurring.

> -- Given a Yahtzee state and a list of dice to keep from the current roll, calculate
> -- the expected score and return the score with a description of the dice we kept.
> computeScoreOnReroll :: DecisionMemo -> DecisionMemo -> YState -> Roll -> IO Decision
> computeScoreOnReroll gmemo lmemo yst keeps =
>   let (partialRolls, partialRollOdds) = unzip (completeRollListWithOdds !! (5 - rollSize keeps - 1))
>       newRolls = map (unionRoll keeps) partialRolls
>       nextTurns = map (YTurn ((rerolls $ turn yst) - 1)) newRolls
>       nextStates = map (\nt -> yst { turn = nt }) nextTurns
>    in do
>         scores <- mapM (expectedScore gmemo lmemo) nextStates
>         let weightedScores = zipWith (\(s, _) -> (s*)) scores partialRollOdds
>         return $ (sum weightedScores, showRoll keeps)
>           where
>             -- Convenience functions for displaying dice rolls in English.
>             showRoll :: Roll -> String
>             showRoll roll = foldl (++) "keep " (map (showDie roll) (distinctFaces roll))
>             showDie roll num =
>               show (occur num roll) ++
>               " " ++
>               show num ++
>               if (occur num roll > 1) then "s," else ","

== Locks, Threads, and Caches, Oh My!

A naïve implementation of the computations described so far will correctly solve for the correct decision for any given Yahtzee state, but it will take forever.
(When I was experimenting, my naïve version started taking on the order of hours to finish when there were only four empty categories on the scorecard.)

=== Memoization

The major design technique we have to speed up the solver is memoization.
Each optimal decision for any state depends on the expected score for lots of other states and we don't want to waste time recalculating any states we've already seen before.
However, if we try to store every single game state in a single memo, we will quickly run out of memory.
The number of possible `Scorecard`s is $2^{13}$ (each of the 13 categories is an on/off switch).
Then we multiply by 2 for whether or not the Yahtzee bonus is active, than by 64 for the number of possible upper category totals (0--63 inclusive), than by the number of possible complete dice rolls (923), and finally by the number of reroll options (0, 1, 2, or 3).

$$2^{13} \times 63 \times 2 \times 923 \times 4 \approx 3.8B$$

Even with only a few bytes per state, we will rapidly run out of memory.
(And I haven't even completely minimized the number of bytes per state---while I did some squeezing of data into bitmaps, I stored strings for describing decisions, which will increase the required storage.)

So we can't store the solution to every possible Yahtzee state.
Luckily, the graph of Yahtzee states has an interesting structure that allows us to store solutions to only a fraction of the possible states.

At the end of any given turn, there are a limited number of successor states: the number of empty categories multiplied by the number of possible dice rolls ($e \times 923$, where $e$ is the number of empty categories).
Every single turn has the same internal structure---an initial roll, followed by choices of rerolls or scoring, and the odds of any given roll or reroll are the same for every turn.
This leads to a graph where there are a number of important "guideposts" (the beginning of turns), and the possible transitions between guideposts have the same structure.

Crucially, the intra-turn states do not affect the expected scores of any state beyond their associated guidepost.
Once we have calculated the expected score for a guidepost, we never need to touch the associated intra-turn states again.
Therefore, the trick to efficient memoization is that we only permanently store the expected scores for the guideposts.
Once that number has been calculated, no other state relies on any states within that turn and we can throw those expected scores away.

However, while we are in the midst of a turn, we still don't want to recalculate state expected scores if we don't have to.
So we use a separate, local memo to store scores for that turn and discard that memo when we're finished.

In the graph below, the guideposts---the beginning of turns---are marked by the empty categories on the scorecard.
The larger box shows the structure of the intra-turn states; hopefully it's clear why they can be discarded after we've calculated the expected score for the initial guidepost.

![Yahtzee state graph](/images/yahtzee-turn-structure.svg)\

This is why our functions are passing around two different memos.
One is the global memo, shared among all function invocations, and one is the local memo, used only for one turn and then discarded.

=== Threading

This graph structure points us to a pretty intuitive threading model: spawn a new thread for each turn.
Each thread will have to coordinate access to the global memo, but will be able to use their own local memo without worrying about contention.
We've already seen the bit of code that spawns new threads---the `mapConcurrently` call in `computeScore`.

=== Locking

But we do have to worry about coordination regarding the global memo.
The logic we want is: when we need to calculate the expected score at the beginning of a turn, we create a new thread (we saw `computeScore` do that with `mapConcurrently`).
The new thread checks if any other thread is working on the same turn---if there is, the new thread waits for the other.
If not, the thread "claims" the turn so no other threads can work on it.

This is what the `TVar` and `TMVar` in the `DecisionMemo` are for.
Recall that the definition is:

```haskell
type DecisionMemo = TVar (Map YState (TMVar Decision))
```

The outer `TVar` protects the entire structure when a thread is checking if there are any other threads working on a particular turn.
If the current `YState` does not exist in the map, there are no other threads---the current thread claims the turn by inserting an empty `TMVar` into the map.
Once the producer thread has finished calculating the turn's expected score, it fills the `TMVar` with the result.
The synchronization is actually fairly straightforward using the STM `atomically` function.

Now we are finally ready to look at the function that does all this.
`expectedScore` is the entry point to our Yahtzee solver.
It does all the bookkeeping described above and then calls `computeScore` for the actual calculation.

> -- The entry point for the Yahtzee solver. Given a state, return the expected score.
> expectedScore :: DecisionMemo -> DecisionMemo -> YState -> IO Decision
> expectedScore gmemo lmemo ystate

The first case we handle is when the `YState` is at the beginning of a turn.
All of those states should be stored in the global memo, so we check if another thread has computed or is computing it.

>   | isBegin (turn ystate) = do
>     (turnlock, iamproducer) <- checkMemoized gmemo ystate
>     if iamproducer
>       then do

If we're the producer, we create a blank local memo and pass it in to `computeScore`.
Note that we force strict evaluation here using the `force` function from `DeepSeq`---Haskell's lazy evaluation is not helpful when we absolutely need the local memo to be garbage collected in a timely manner to avoid running out of memory.

>         newlmemo <- emptymemo
>         computedscore <- computeScore gmemo newlmemo ystate
>         let !evaluated = force computedscore
>         atomically $ do
>           writeTVar newlmemo Map.empty
>           putTMVar turnlock evaluated
>           readTMVar turnlock

If we're not the producer, we just read from lock that `checkMemoized` returned for us.
`readTMVar` will block until the other thread has computed the decision and put it in the lock.

>       else atomically $ readTMVar turnlock

So what if the `YState` is in the midst of a turn?
It could still be memoized!
Even though the local memo only lives as long as we're computing turns within the same state, we'll still need to compute states several times.

>   | otherwise = do
>     (turnlock, iamproducer) <- checkMemoized lmemo ystate
>     if iamproducer
>       then do

But if we need to compute the score ourselves, we reuse the same local memo.

>         computedscore <- computeScore gmemo lmemo ystate
>         atomically $ putTMVar turnlock computedscore
>         atomically $ readTMVar turnlock
>       else atomically $ readTMVar turnlock
>   where
>     checkMemoized :: DecisionMemo -> YState -> IO (TMVar Decision, Bool)

`checkMemoized` 1) checks if the `YState` has been memoized and 2) returns the `TMVar` to read from.
`checkMemoized` returns `True` if the caller needs to compute the decision themselves.
If `False`, another thread is computing the decision and the current one should block until the decision is available.
This is the only time where we care about the external `TVar`---it is there to make sure that only one thread can claim computation of a particular `YState`.

>     checkMemoized memo ystate = atomically $ do
>       map <- readTVar memo
>       case Map.lookup ystate map of
>         Just lock -> return (lock, False)
>         Nothing   -> do
>           emptylock <- newEmptyTMVar
>           writeTVar memo (Map.insert ystate emptylock map)
>           return (emptylock, True)

= Serialization

It seems a shame to do all this computation every time we run the program, so I added some basic serialization and storage.
This requires us to implement the `Binary` typeclass for each type we want to serialize.
I used the absolute simplest implementations possible.
Check out the [Data.Binary](https://hackage.haskell.org/package/binary-0.8.9.3/docs/Data-Binary.html) documentation for how this works.

> instance Binary Scorecard where
>   put (Scorecard w) = put w
>   get = Scorecard <$> get
>
> instance Binary Roll where
>   put (Roll w) = put w
>   get = Roll <$> get
>
> instance Binary YTurn where
>   put (YTurn rr r) = put rr >> put r
>   get = YTurn <$> get <*> get
>
> instance Binary YState where
>   put (YState c ut b t) = put c >> put ut >> put b >> put t
>   get = YState <$> get <*> get <*> get <*> get

Once the `Binary` typeclass is implemented, the `saveMemo` and `loadMemo` functions relatively easy to write.

> -- write a DecisionMemo to a file
> saveMemo :: DecisionMemo -> FilePath -> IO ()
> saveMemo memo filepath = do
>   memoMap <- atomically $ readTVar memo
>   -- Extract decisions from TMVars (only those that are filled)
>   decisions <- atomically $ do
>     let entries = Map.toList memoMap
>     filledEntries <- mapM tryReadEntry entries
>     return $ Map.fromList [(k, v) | (k, Just v) <- filledEntries]
>   encodeFile filepath decisions
>   where
>     tryReadEntry :: (YState, TMVar Decision) -> STM (YState, Maybe Decision)
>     tryReadEntry (ystate, tmvar) = do
>       isEmpty <- isEmptyTMVar tmvar
>       if isEmpty
>         then return (ystate, Nothing)
>         else do
>           decision <- readTMVar tmvar
>           return (ystate, Just decision)
>
> -- load a DecisionMemo from a file
> loadMemo :: FilePath -> IO DecisionMemo
> loadMemo filepath = do
>   decisions <- decodeFile filepath :: IO (Map YState Decision)
>   atomically $ do
>     memoMap <- mapM fillEntry (Map.toList decisions)
>     newTVar (Map.fromList memoMap)
>   where
>     fillEntry :: (YState, Decision) -> STM (YState, TMVar Decision)
>     fillEntry (ystate, decision) = do
>       tmvar <- newTMVar decision
>       return (ystate, tmvar)

= Finally, A Main Function

Our main function is as barebones as can be and the UI is just about usable.

It reads a line at a time, with each element in the line separated by spaces.

- The first 13 elements mark whether each category is used: an `-` for unused and an `x` for used. The categories are in the standard Yahtzee scorecard order: ones, twos, threes, fours, fives, sixes, three-of-a-kind, four-of-a-kind, full house, small straight, large straight, Yahtzee, chance.
- The next is the upper total.
- Then whether the Yahtzee Bonus is active (`True` or `False`).
- Then how many rerolls are left in the current turn.
- The last five elements represent the dice roll.

For example:

```bash
echo '- x x x x x x x x x x - x 62 False 2 1 2 2 2 6' | stack ysolver.lhs
```

calculates what the best option is when:

- The ones and Yahtzee categories are empty, and all others are used.
- The upper category total is 62.
- The next Yahtzee will not earn a bonus.
- We have two rolls left in our current turn.
- We just rolled one 1, three 2s, and a 6.

The question is how we balance trying to achieve a Yahtzee (presumably using the 2s) versus taking the safe option of hitting our bonus by scoring a 1 in the ones category.

For the curious: solving the starting position from scratch with no precomputation took 33 hours.
Glenn comments that his version, written in C++, took an hour; I am not sure how to match that, other than giving up on Haskell.
The size of the resulting complete memoization file is 56MB, but any further computations take fractions of a second.
56MB is larger than necessary---removing or minimizing the strings from the `Decision` datatype would cut down the size significantly.

> main :: IO ()
> main = do
>   memoFileExists <- doesFileExist "yahtzee.memo"
>   gmemo <- if memoFileExists
>              then loadMemo "yahtzee.memo"
>              else emptymemo
>   loop gmemo
>   where
>     loop global = do
>       end <- isEOF
>       if end
>         then return ()
>         else do
>           input <- getLine
>           let ystate = parseInput input
>           local <- emptymemo
>           result <- expectedScore global local ystate
>           putStrLn $ show result
>           saveMemo global "yahtzee.memo"
>           loop global

Our parsing function does zero validation or error checking.

> parseInput :: String -> YState
> parseInput line =
>   let ws = words line
>       scWords = take 13 ws
>       allCatsWithMark = zip allCats scWords
>       sc = foldl' (\acc (c, l) -> if l == "x" then fill c acc else acc) emptycard allCatsWithMark
>       ut = read $ ws !! 13
>       b = read $ ws !! 14
>       rr = read $ ws !! 15
>       rollWords = drop 16 ws
>       roll = listToFullRoll $ [read w | w <- rollWords]
>    in YState { card = sc, uptotal = ut, bonus = b, turn = YTurn { rerolls = rr, roll = roll } }

= Appendix: Various Scoring Functions

I relegated all of the various functions for scoring a dice roll to the end.
They were easy to write, but not particularly interesting.

If the Yahtzee bonus is active, a Yahtzee roll gets an extra 100 points no matter what category it is scored in.

> scoreRollWithBonus :: YBonus -> Roll -> Category -> Int
> scoreRollWithBonus True roll cat =
>   let bonus = if (isYahtzee roll) then 100 else 0
>    in bonus + scoreRoll roll cat
> scoreRollWithBonus False roll cat = scoreRoll roll cat

Our score roll function is dumb but simple---just pattern matching on each possible category.

> scoreRoll :: Roll -> Category -> Int
> scoreRoll dice Ones = occur 1 dice
> scoreRoll dice Twos = (occur 2 dice) * 2
> scoreRoll dice Threes = (occur 3 dice) * 3
> scoreRoll dice Fours = (occur 4 dice) * 4
> scoreRoll dice Fives = (occur 5 dice) * 5
> scoreRoll dice Sixes = (occur 6 dice) * 6
> scoreRoll dice ThreeKind = if atLeastNTimes 3 dice then (sumRoll dice) else 0
> scoreRoll dice FourKind = if atLeastNTimes 4 dice then (sumRoll dice) else 0
> scoreRoll dice FullHouse = if isFullHouse dice then 25 else 0
> scoreRoll dice SmStraight = if isSmStraight dice then 30 else 0
> scoreRoll dice LgStraight = if isLgStraight dice then 40 else 0
> scoreRoll dice Yahtzee = if isYahtzee dice then 50 else 0
> scoreRoll dice Chance = sumRoll dice
>
> atLeastNTimes :: Int -> Roll -> Bool
> atLeastNTimes n roll = any (\i -> occur i roll >= n) [1..6]
>
> isFullHouse :: Roll -> Bool
> isFullHouse dice =
>   let distinctDice = distinctFaces dice
>       diceOccur k = occur k dice
>       occurList = sort $ map diceOccur distinctDice
>    in occurList == [2, 3]
>
> isSmStraight :: Roll -> Bool
> isSmStraight dice =
>   any isConsecutive (windows uniqDice)

The small straight detection is mildly complicated by needing to check if either "window" of dice contains four consecutive dice.

>   where
>     uniqDice = sort $ distinctFaces dice
>     isConsecutive [a, b, c, d] = a + 1 == b && b + 1 == c && c + 1 == d
>     isConsecutive _ = False
>     windows xs | length xs < 4 = [] | otherwise = take 4 xs : windows (drop 1 xs)
>
> isLgStraight :: Roll -> Bool
> isLgStraight dice =
>   isConsecutive uniqDice
>   where
>     uniqDice = sort $ distinctFaces dice

This version of the `isConsecutive` function only handles five dice because a large straight must use all five dice.

>     isConsecutive [a, b, c, d, e] = a + 1 == b && b + 1 == c && c + 1 == d && d + 1 == e
>     isConsecutive _ = False
>
> isYahtzee :: Roll -> Bool
> isYahtzee dice = length (distinctFaces dice) == 1
>
> sumRoll :: Roll -> Int
> sumRoll roll = sum [i * occur i roll | i <- [1..6]]

