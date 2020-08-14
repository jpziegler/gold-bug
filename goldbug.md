module goldbug where

/** The goldbug cipher uses several non-ASCII characters */
type Char = [16]
type String n = [n]Char
type Key nk = [2](String nk)

/** Applies the substitution cipher defined by key to a character */
cipher_char : {nk} fin nk => Key nk -> Char -> Char
cipher_char [ks,vs] c = search!0
  where search = [c] # [ if k == c then v else prev
                 | prev <- search | k <- ks | v <- vs ]

/** Applies the substitution cipher defined by key to a string */
cipher : {n, nk} fin nk => Key nk -> String n -> String n
cipher key = map (cipher_char key)

/** cryptogram in _The Gold-Bug_ */
goldbug_ct : String 203
goldbug_ct = 
    "53‡‡†305))6*;4826)4‡.)4‡);80" #
    "6*;48†8¶60))85;1‡(;:‡*8†83(88)" #
    "5*†;46(;88*96*?;8)*‡(;485);5*†" #
    "2:*‡(;4956*2(5*-4)8¶8*;40692" #
    "85);)6†8)4‡‡;1(‡9;48081;8:8‡1" #
    ";48†85;4)485†528806*81(‡9;48" #
    ";(88;4(‡?34;48)4‡;161;:188;‡?;"

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

/** partial key narrated in _The Gold-Bug_ */
goldbug_partial_key : Key 10
goldbug_partial_key = ["5†8346*‡(;", "ADEGHINORT"]
/** partially deciphered plaintext implied in _The Gold-Bug_ */
goldbug_partial_pt = cipher goldbug_partial_key goldbug_ct

/** Returns true if the list is a sorted set of unique elements */
is_sorted_set xs = and [a < b | a <- xs | b <- tail xs]

/** Full key derived from matched PT/CT
Found with the following solver invocation: 
:sat \(k:Key 20) -> cipher k goldbug_ct == goldbug_pt /\ is_sorted_set (k@1)
20 is the minimum satisfiable key size. (Six letters are not represented.) */
goldbug_full_key : Key 20
goldbug_full_key = ["52-†8134609*‡.();?¶:", "ABCDEFGHILMNOPRSTUVY"]
property goldbug_full_key_is_correct =
  cipher goldbug_full_key goldbug_ct == goldbug_pt
