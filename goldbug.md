# The Gold-Bug Cryptogram
This document represents the cryptogram from Edgar Allen Poe's short story [The Gold-Bug](https://poestories.com/read/goldbug).

The module is a [literate](https://en.wikipedia.org/wiki/Literate_programming) [Cryptol](https://cryptol.net/) document and can be executed using the Cryptol interpreter.

Quoted excerpts from the original text are presented alongside relevant code segments.

We begin with a module declaration and some types.

```cryptol
module goldbug where

type Char = [8]
type String n = [n]Char
type Key nk = [2](String nk)
```

We begin our story at the point when William Legrand reveals the cryptogram.

> "I held the vellum again to the fire, after increasing the heat; but nothing appeared. I now thought it possible that the coating of dirt might have something to do with the failure; so I carefully rinsed the parchment by pouring warm water over it, and, having done this, I placed it in a tin pan, with the skull downwards, and put the pan upon a furnace of lighted charcoal. In a few minutes, the pan having become thoroughly heated, I removed the slip, and, to my inexpressible joy, found it spotted, in several places, with what appeared to be figures arranged in lines. Again I placed it in the pan, and suffered it to remain another minute. On taking it off, the whole was just as you see it now."
>
>Here Legrand, having re-heated the parchment, submitted It my inspection. The following characters were rudely traced, in a red tint, between the death's-head and the goat:

```cryptol
/** cryptogram in _The Gold-Bug_ */
goldbug_ct : String 203
goldbug_ct = 
    "53==+305))6*;4826)4=.)4=);80" #
    "6*;48+8¶60))85;1=(;:=*8+83(88)" #
    "5*+;46(;88*96*?;8)*=(;485);5*+" #
    "2:*=(;4956*2(5*-4)8¶8*;40692" #
    "85);)6+8)4==;1(=9;48081;8:8=1" #
    ";48+85;4)485+528806*81(=9;48" #
    ";(88;4(=?34;48)4=;161;:188;=?;"
```

>"But," said I, returning him the slip, "I am as much in the dark as ever. Were all the jewels of Golconda awaiting me on my solution of this enigma, I am quite sure that I should be unable to earn them."

>"And yet," said Legrand, "the solution is by no means so difficult as you might be led to imagine from the first hasty inspection of the characters. These characters, as any one might readily guess, form a cipher --that is to say, they convey a meaning; but then, from what is known of Kidd, I could not suppose him capable of constructing any of the more abstruse cryptographs. I made up my mind, at once, that this was of a simple species --such, however, as would appear, to the crude intellect of the sailor, absolutely insoluble without the key."

```
/** Applies the substitution cipher defined by key to a character */
cipher_char : {nk} fin nk => Key nk -> Char -> Char
cipher_char [ks,vs] c = search!0
  where search = [c] # [ if k == c then v else prev
                 | prev <- search | k <- ks | v <- vs ]

/** Applies the substitution cipher defined by key to a string */
cipher : {n, nk} fin nk => Key nk -> String n -> String n
cipher key = map (cipher_char key)
```

At this point, Legrand steps us through his reasoning by which he cracks the cipher.

>"To avoid confusion, it is now time that we arrange our key, as far as discovered, in a tabular form. It will stand thus:"

```cryptol
/** partial key narrated in _The Gold-Bug_ */
goldbug_partial_key : Key 10
goldbug_partial_key = ["5+8346*=(;", "ADEGHINORT"]

/** partially deciphered plaintext implied in _The Gold-Bug_ */
goldbug_partial_pt = cipher goldbug_partial_key goldbug_ct
```

>"We have, therefore, no less than ten of the most important letters represented, and it will be unnecessary to proceed with the details of the solution. I have said enough to convince you that ciphers of this nature are readily soluble, and to give you some insight into the rationale of their development. But be assured that the specimen before us appertains to the very simplest species of cryptograph. It now only remains to give you the full translation of the characters upon the parchment, as unriddled. Here it is:"

```cryptol
/** Solution to cryptogram in _The Gold-Bug_ */
goldbug_pt : String 203
goldbug_pt =
    "AGOODGLASSINTHEBISHOPSHOSTEL" #
    "INTHEDEVILSSEATFORTYONEDEGREES" #
    "ANDTHIRTEENMINUTESNORTHEASTANDBYNORTH" #
    "MAINBRANCHSEVENTHLIMBEASTSIDE" #
    "SHOOTFROMTHELEFTEYEOFTHEDEATHSHEAD" #
    "ABEELINEFROMTHETREE" #
    "THROUGHTHESHOTFIFTYFEETOUT"
```

In story, the reader is given only the partial key (10 characters). However, using the matched plaintext and ciphertext, Cryptol's solver functionality can easily derive the full key with minimal coding.

We begin with a small helper function to ensure that the solution is presented in alphabetical order.

```cryptol
/** Returns true if the list is a sorted set of unique elements */
is_sorted xs = and [a < b | a <- xs | b <- tail xs]
```

The following solver invocation discovers the solution. Simple experimentation demonstrates that 20 is the minimum satisfiable key size. This is because six letters of the alphabet (J, K, Q, W, X, and Z) are not represented.

```interpreter
Cryptol> :l goldbug.md
goldbug> :sat \(k:Key 20) -> cipher k goldbug_ct == goldbug_pt /\ is_sorted (k@1)
```

The following property shows that the discovered key `goldbug_full_key` is in fact correct.

```cryptol
/** Full key derived from matched PT/CT */
goldbug_full_key : Key 20
goldbug_full_key = ["52-+8134609*=.();?¶:", "ABCDEFGHILMNOPRSTUVY"]
property goldbug_full_key_is_correct =
  cipher goldbug_full_key goldbug_ct == goldbug_pt
```

And the invocation:

```interpreter
goldbug> :prove goldbug_full_key_is_correct
```