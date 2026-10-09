-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair021_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:11:37.785222+00:00
-- url     : https://prove2.me/submissions/24a73785-555a-41f1-a500-b91b3fa4c2cf

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
import Mathlib.Tactic


set_option autoImplicit false
namespace Helfgott

lemma mobiusTreeCheck_join (g : ℕ → ℤ) (B d offset : ℕ) (l r : MobiusCertTree)
    (hl : mobiusTreeCheck g B d offset l = true)
    (hr : mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true) :
    mobiusTreeCheck g B (d + 1) offset (.branch l r) = true := by
  by_cases hoff : B ≤ offset
  · simp [mobiusTreeCheck, hoff]
  · simpa [mobiusTreeCheck, hoff] using And.intro hl hr

lemma mobiusHarmonicTreeCheck_join (g M : ℕ → ℤ) (Q B d offset upper : ℕ)
    (l r : MobiusHarmonicTree) (hoff : offset < B)
    (hl : mobiusHarmonicTreeCheck g M Q B d offset l = true)
    (hr : mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true)
    (hu : upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r) :
    mobiusHarmonicTreeCheck g M Q B (d + 1) offset (.branch upper l r) = true := by
  have hoff' : ¬B ≤ offset := not_le.mpr hoff
  simpa [mobiusHarmonicTreeCheck, hoff', Bool.and_assoc, and_assoc] using ⟨hl, hr, hu⟩

end Helfgott
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Helfgott

private abbrev cg : ℕ → ℤ := mobiusTreeValue 16 mobiusTable1200001
private abbrev cm : ℕ → ℤ := mobiusPrefixValue 16 mobiusHarmonic1078853

private def publishedLeaf : ℕ → MobiusHarmonicTree → ℕ → MobiusHarmonicTree
  | 0, tree, _ => tree
  | d + 1, .branch _ l r, k =>
      if k < 2 ^ d then publishedLeaf d l k else publishedLeaf d r (k - 2 ^ d)
  | _, tree, _ => tree

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344064 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344128 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 69564283 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344192 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344256 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 73491879 d11 d12
private def d6 : MobiusHarmonicTree := .branch 143056162 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344320 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344384 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 75671581 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344448 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344512 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 73068852 d18 d19
private def d13 : MobiusHarmonicTree := .branch 148740433 d14 d17
private def d5 : MobiusHarmonicTree := .branch 291796595 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344576 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344640 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 70328687 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344704 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344768 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 69174231 d26 d27
private def d21 : MobiusHarmonicTree := .branch 139502918 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344832 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344896 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 68739643 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344960 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345024 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 74168941 d33 d34
private def d28 : MobiusHarmonicTree := .branch 142908584 d29 d32
private def d20 : MobiusHarmonicTree := .branch 282411502 d21 d28
private def d4 : MobiusHarmonicTree := .branch 574208097 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345088 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345152 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 74225458 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345216 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345280 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 72538383 d42 d43
private def d37 : MobiusHarmonicTree := .branch 146763841 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345344 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345408 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 67650625 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345472 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345536 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 69555730 d49 d50
private def d44 : MobiusHarmonicTree := .branch 137206355 d45 d48
private def d36 : MobiusHarmonicTree := .branch 283970196 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345600 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345664 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 71245712 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345728 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345792 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 70848999 d57 d58
private def d52 : MobiusHarmonicTree := .branch 142094711 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345856 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345920 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 70840228 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 345984 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346048 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 69499113 d64 d65
private def d59 : MobiusHarmonicTree := .branch 140339341 d60 d63
private def d51 : MobiusHarmonicTree := .branch 282434052 d52 d59
private def d35 : MobiusHarmonicTree := .branch 566404248 d36 d51
private def d3 : MobiusHarmonicTree := .branch 1140612345 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346112 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346176 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 74046273 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346240 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346304 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 73302833 d74 d75
private def d69 : MobiusHarmonicTree := .branch 147349106 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346368 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346432 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 74378197 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346496 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346560 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 78999434 d81 d82
private def d76 : MobiusHarmonicTree := .branch 153377631 d77 d80
private def d68 : MobiusHarmonicTree := .branch 300726737 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346624 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346688 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 79916411 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346752 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346816 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 82323413 d89 d90
private def d84 : MobiusHarmonicTree := .branch 162239824 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346880 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 346944 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 82062484 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347008 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347072 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 81991707 d96 d97
private def d91 : MobiusHarmonicTree := .branch 164054191 d92 d95
private def d83 : MobiusHarmonicTree := .branch 326294015 d84 d91
private def d67 : MobiusHarmonicTree := .branch 627020752 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347136 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347200 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 83943057 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347264 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347328 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 82164810 d105 d106
private def d100 : MobiusHarmonicTree := .branch 166107867 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347392 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347456 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 75618581 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347520 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347584 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 75363201 d112 d113
private def d107 : MobiusHarmonicTree := .branch 150981782 d108 d111
private def d99 : MobiusHarmonicTree := .branch 317089649 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347648 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347712 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 75416024 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347776 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347840 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 74669655 d120 d121
private def d115 : MobiusHarmonicTree := .branch 150085679 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347904 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 347968 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 75233944 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348032 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348096 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 80963559 d127 d128
private def d122 : MobiusHarmonicTree := .branch 156197503 d123 d126
private def d114 : MobiusHarmonicTree := .branch 306283182 d115 d122
private def d98 : MobiusHarmonicTree := .branch 623372831 d99 d114
private def d66 : MobiusHarmonicTree := .branch 1250393583 d67 d98
private def d2 : MobiusHarmonicTree := .branch 2391005928 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348160 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348224 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 76921965 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348288 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348352 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 73494875 d138 d139
private def d133 : MobiusHarmonicTree := .branch 150416840 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348416 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348480 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 77066240 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348544 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348608 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 74998466 d145 d146
private def d140 : MobiusHarmonicTree := .branch 152064706 d141 d144
private def d132 : MobiusHarmonicTree := .branch 302481546 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348672 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348736 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 76318596 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348800 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348864 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 74728461 d153 d154
private def d148 : MobiusHarmonicTree := .branch 151047057 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348928 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 348992 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 75113744 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349056 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349120 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 72539750 d160 d161
private def d155 : MobiusHarmonicTree := .branch 147653494 d156 d159
private def d147 : MobiusHarmonicTree := .branch 298700551 d148 d155
private def d131 : MobiusHarmonicTree := .branch 601182097 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349184 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349248 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 71880436 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349312 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349376 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 72506359 d169 d170
private def d164 : MobiusHarmonicTree := .branch 144386795 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349440 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349504 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 73058056 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349568 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349632 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 73797720 d176 d177
private def d171 : MobiusHarmonicTree := .branch 146855776 d172 d175
private def d163 : MobiusHarmonicTree := .branch 291242571 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349696 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349760 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 76729844 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349824 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349888 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 80837397 d184 d185
private def d179 : MobiusHarmonicTree := .branch 157567241 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 349952 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350016 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 80819502 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350080 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350144 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 79738815 d191 d192
private def d186 : MobiusHarmonicTree := .branch 160558317 d187 d190
private def d178 : MobiusHarmonicTree := .branch 318125558 d179 d186
private def d162 : MobiusHarmonicTree := .branch 609368129 d163 d178
private def d130 : MobiusHarmonicTree := .branch 1210550226 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350208 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350272 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 80905827 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350336 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350400 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 83210665 d201 d202
private def d196 : MobiusHarmonicTree := .branch 164116492 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350464 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350528 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 86846226 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350592 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350656 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 88442995 d208 d209
private def d203 : MobiusHarmonicTree := .branch 175289221 d204 d207
private def d195 : MobiusHarmonicTree := .branch 339405713 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350720 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350784 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 88846861 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350848 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350912 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 85939334 d216 d217
private def d211 : MobiusHarmonicTree := .branch 174786195 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 350976 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351040 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 85389196 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351104 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351168 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 84646385 d223 d224
private def d218 : MobiusHarmonicTree := .branch 170035581 d219 d222
private def d210 : MobiusHarmonicTree := .branch 344821776 d211 d218
private def d194 : MobiusHarmonicTree := .branch 684227489 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351232 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351296 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 85927643 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351360 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351424 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 87395994 d232 d233
private def d227 : MobiusHarmonicTree := .branch 173323637 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351488 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351552 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 85583696 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351616 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351680 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 84773024 d239 d240
private def d234 : MobiusHarmonicTree := .branch 170356720 d235 d238
private def d226 : MobiusHarmonicTree := .branch 343680357 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351744 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351808 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 87192671 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351872 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 351936 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 84160559 d247 d248
private def d242 : MobiusHarmonicTree := .branch 171353230 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352000 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352064 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 81329059 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352128 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock042 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352192 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 80283207 d254 d255
private def d249 : MobiusHarmonicTree := .branch 161612266 d250 d253
private def d241 : MobiusHarmonicTree := .branch 332965496 d242 d249
private def d225 : MobiusHarmonicTree := .branch 676645853 d226 d241
private def d193 : MobiusHarmonicTree := .branch 1360873342 d194 d225
private def d129 : MobiusHarmonicTree := .branch 2571423568 d130 d193
private def d1 : MobiusHarmonicTree := .branch 4962429496 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352256 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352320 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 77935095 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352384 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352448 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 79189231 d266 d267
private def d261 : MobiusHarmonicTree := .branch 157124326 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352512 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352576 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 78054304 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352640 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352704 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 73288389 d273 d274
private def d268 : MobiusHarmonicTree := .branch 151342693 d269 d272
private def d260 : MobiusHarmonicTree := .branch 308467019 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352768 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352832 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 72649572 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352896 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 352960 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 68883401 d281 d282
private def d276 : MobiusHarmonicTree := .branch 141532973 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353024 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353088 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 66332059 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353152 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353216 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 66644916 d288 d289
private def d283 : MobiusHarmonicTree := .branch 132976975 d284 d287
private def d275 : MobiusHarmonicTree := .branch 274509948 d276 d283
private def d259 : MobiusHarmonicTree := .branch 582976967 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353280 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353344 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 65248189 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353408 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353472 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 68477879 d297 d298
private def d292 : MobiusHarmonicTree := .branch 133726068 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353536 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353600 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 70486577 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353664 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353728 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 71391172 d304 d305
private def d299 : MobiusHarmonicTree := .branch 141877749 d300 d303
private def d291 : MobiusHarmonicTree := .branch 275603817 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353792 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353856 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 69285523 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353920 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 353984 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 71895955 d312 d313
private def d307 : MobiusHarmonicTree := .branch 141181478 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354048 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354112 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 74713862 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354176 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354240 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 73693161 d319 d320
private def d314 : MobiusHarmonicTree := .branch 148407023 d315 d318
private def d306 : MobiusHarmonicTree := .branch 289588501 d307 d314
private def d290 : MobiusHarmonicTree := .branch 565192318 d291 d306
private def d258 : MobiusHarmonicTree := .branch 1148169285 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354304 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354368 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 78861546 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354432 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354496 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 81924877 d329 d330
private def d324 : MobiusHarmonicTree := .branch 160786423 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354560 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354624 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 81531647 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354688 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354752 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 83311933 d336 d337
private def d331 : MobiusHarmonicTree := .branch 164843580 d332 d335
private def d323 : MobiusHarmonicTree := .branch 325630003 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354816 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354880 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 81968760 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 354944 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355008 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 83313608 d344 d345
private def d339 : MobiusHarmonicTree := .branch 165282368 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355072 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355136 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 89208222 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355200 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355264 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 87988239 d351 d352
private def d346 : MobiusHarmonicTree := .branch 177196461 d347 d350
private def d338 : MobiusHarmonicTree := .branch 342478829 d339 d346
private def d322 : MobiusHarmonicTree := .branch 668108832 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355328 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355392 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 89183537 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355456 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355520 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 90675750 d360 d361
private def d355 : MobiusHarmonicTree := .branch 179859287 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355584 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355648 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 90151131 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355712 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355776 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 90470099 d367 d368
private def d362 : MobiusHarmonicTree := .branch 180621230 d363 d366
private def d354 : MobiusHarmonicTree := .branch 360480517 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355840 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355904 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 89220977 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 355968 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356032 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 86062815 d375 d376
private def d370 : MobiusHarmonicTree := .branch 175283792 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356096 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356160 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 85245496 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356224 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356288 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 87039283 d382 d383
private def d377 : MobiusHarmonicTree := .branch 172284779 d378 d381
private def d369 : MobiusHarmonicTree := .branch 347568571 d370 d377
private def d353 : MobiusHarmonicTree := .branch 708049088 d354 d369
private def d321 : MobiusHarmonicTree := .branch 1376157920 d322 d353
private def d257 : MobiusHarmonicTree := .branch 2524327205 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356352 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356416 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 83980843 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356480 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356544 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 85821263 d393 d394
private def d388 : MobiusHarmonicTree := .branch 169802106 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356608 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356672 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 82151474 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356736 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356800 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 76858463 d400 d401
private def d395 : MobiusHarmonicTree := .branch 159009937 d396 d399
private def d387 : MobiusHarmonicTree := .branch 328812043 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356864 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356928 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 77290255 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 356992 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357056 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 76923670 d408 d409
private def d403 : MobiusHarmonicTree := .branch 154213925 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357120 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357184 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 74726484 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357248 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357312 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 71996045 d415 d416
private def d410 : MobiusHarmonicTree := .branch 146722529 d411 d414
private def d402 : MobiusHarmonicTree := .branch 300936454 d403 d410
private def d386 : MobiusHarmonicTree := .branch 629748497 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357376 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357440 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 71606636 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357504 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357568 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 71871841 d424 d425
private def d419 : MobiusHarmonicTree := .branch 143478477 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357632 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357696 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 72167436 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357760 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357824 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 75811149 d431 d432
private def d426 : MobiusHarmonicTree := .branch 147978585 d427 d430
private def d418 : MobiusHarmonicTree := .branch 291457062 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357888 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 357952 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 72736186 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358016 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358080 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 71082140 d439 d440
private def d434 : MobiusHarmonicTree := .branch 143818326 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358144 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358208 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 69926036 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358272 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358336 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 73219042 d446 d447
private def d441 : MobiusHarmonicTree := .branch 143145078 d442 d445
private def d433 : MobiusHarmonicTree := .branch 286963404 d434 d441
private def d417 : MobiusHarmonicTree := .branch 578420466 d418 d433
private def d385 : MobiusHarmonicTree := .branch 1208168963 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358400 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358464 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 76972960 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358528 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358592 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 75935974 d456 d457
private def d451 : MobiusHarmonicTree := .branch 152908934 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358656 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358720 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 81054871 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358784 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358848 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 81015187 d463 d464
private def d458 : MobiusHarmonicTree := .branch 162070058 d459 d462
private def d450 : MobiusHarmonicTree := .branch 314978992 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358912 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 358976 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 80356416 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359040 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359104 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 79656957 d471 d472
private def d466 : MobiusHarmonicTree := .branch 160013373 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359168 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359232 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 76944995 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359296 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359360 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 75058666 d478 d479
private def d473 : MobiusHarmonicTree := .branch 152003661 d474 d477
private def d465 : MobiusHarmonicTree := .branch 312017034 d466 d473
private def d449 : MobiusHarmonicTree := .branch 626996026 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359424 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359488 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 71582577 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359552 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359616 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 71039827 d487 d488
private def d482 : MobiusHarmonicTree := .branch 142622404 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359680 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359744 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 69569166 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359808 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359872 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 66473862 d494 d495
private def d489 : MobiusHarmonicTree := .branch 136043028 d490 d493
private def d481 : MobiusHarmonicTree := .branch 278665432 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 359936 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360000 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 59378021 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360064 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360128 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 57432671 d502 d503
private def d497 : MobiusHarmonicTree := .branch 116810692 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360192 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360256 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 56257321 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360320 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock043 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360384 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 56956129 d509 d510
private def d504 : MobiusHarmonicTree := .branch 113213450 d505 d508
private def d496 : MobiusHarmonicTree := .branch 230024142 d497 d504
private def d480 : MobiusHarmonicTree := .branch 508689574 d481 d496
private def d448 : MobiusHarmonicTree := .branch 1135685600 d449 d480
private def d384 : MobiusHarmonicTree := .branch 2343854563 d385 d448
private def d256 : MobiusHarmonicTree := .branch 4868181768 d257 d384
private def d0 : MobiusHarmonicTree := .branch 9830611264 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 344064 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 344064 9830611264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 344064 4962429496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 344064 2391005928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 344064 1140612345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 344064 574208097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 344064 291796595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 344064 143056162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344064 69564283 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344192 73491879 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 344320 148740433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344320 75671581 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344448 73068852 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 344576 282411502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 344576 139502918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344576 70328687 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344704 69174231 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 344832 142908584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344832 68739643 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 344960 74168941 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 345088 566404248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 345088 283970196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 345088 146763841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345088 74225458 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345216 72538383 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 345344 137206355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345344 67650625 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345472 69555730 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 345600 282434052 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 345600 142094711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345600 71245712 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345728 70848999 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 345856 140339341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345856 70840228 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 345984 69499113 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 346112 1250393583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 346112 627020752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 346112 300726737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 346112 147349106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 346112 74046273 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 346240 73302833 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 346368 153377631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 346368 74378197 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 346496 78999434 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 346624 326294015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 346624 162239824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 346624 79916411 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 346752 82323413 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 346880 164054191 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 346880 82062484 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347008 81991707 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 347136 623372831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 347136 317089649 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 347136 166107867 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347136 83943057 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347264 82164810 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 347392 150981782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347392 75618581 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347520 75363201 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 347648 306283182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 347648 150085679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347648 75416024 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347776 74669655 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 347904 156197503 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 347904 75233944 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348032 80963559 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 348160 2571423568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 348160 1210550226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 348160 601182097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 348160 302481546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 348160 150416840 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348160 76921965 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348288 73494875 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 348416 152064706 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348416 77066240 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348544 74998466 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 348672 298700551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 348672 151047057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348672 76318596 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348800 74728461 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 348928 147653494 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 348928 75113744 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349056 72539750 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 349184 609368129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 349184 291242571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 349184 144386795 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349184 71880436 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349312 72506359 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 349440 146855776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349440 73058056 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349568 73797720 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 349696 318125558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 349696 157567241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349696 76729844 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349824 80837397 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 349952 160558317 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 349952 80819502 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350080 79738815 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 350208 1360873342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 350208 684227489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 350208 339405713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 350208 164116492 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350208 80905827 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350336 83210665 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 350464 175289221 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350464 86846226 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350592 88442995 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 350720 344821776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 350720 174786195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350720 88846861 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350848 85939334 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 350976 170035581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 350976 85389196 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 351104 84646385 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 351232 676645853 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 351232 343680357 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 351232 173323637 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 351232 85927643 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 351360 87395994 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 351488 170356720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 351488 85583696 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 351616 84773024 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 351744 332965496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 351744 171353230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 351744 87192671 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 351872 84160559 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 352000 161612266 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352000 81329059 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352128 80283207 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 352256 4868181768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 352256 2524327205 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 352256 1148169285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 352256 582976967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 352256 308467019 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 352256 157124326 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352256 77935095 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352384 79189231 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 352512 151342693 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352512 78054304 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352640 73288389 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 352768 274509948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 352768 141532973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352768 72649572 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 352896 68883401 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 353024 132976975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353024 66332059 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353152 66644916 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 353280 565192318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 353280 275603817 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 353280 133726068 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353280 65248189 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353408 68477879 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 353536 141877749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353536 70486577 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353664 71391172 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 353792 289588501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 353792 141181478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353792 69285523 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 353920 71895955 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 354048 148407023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354048 74713862 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354176 73693161 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 354304 1376157920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 354304 668108832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 354304 325630003 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 354304 160786423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354304 78861546 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354432 81924877 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 354560 164843580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354560 81531647 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354688 83311933 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 354816 342478829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 354816 165282368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354816 81968760 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 354944 83313608 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 355072 177196461 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355072 89208222 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355200 87988239 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 355328 708049088 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 355328 360480517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 355328 179859287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355328 89183537 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355456 90675750 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 355584 180621230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355584 90151131 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355712 90470099 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 355840 347568571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 355840 175283792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355840 89220977 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 355968 86062815 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 356096 172284779 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356096 85245496 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356224 87039283 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 356352 2343854563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 356352 1208168963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 356352 629748497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 356352 328812043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 356352 169802106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356352 83980843 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356480 85821263 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 356608 159009937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356608 82151474 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356736 76858463 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 356864 300936454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 356864 154213925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356864 77290255 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 356992 76923670 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 357120 146722529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 357120 74726484 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 357248 71996045 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 357376 578420466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 357376 291457062 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 357376 143478477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 357376 71606636 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 357504 71871841 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 357632 147978585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 357632 72167436 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 357760 75811149 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 357888 286963404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 357888 143818326 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 357888 72736186 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358016 71082140 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 358144 143145078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358144 69926036 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358272 73219042 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 358400 1135685600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 358400 626996026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 358400 314978992 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 358400 152908934 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358400 76972960 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358528 75935974 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 358656 162070058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358656 81054871 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358784 81015187 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 358912 312017034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 358912 160013373 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 358912 80356416 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359040 79656957 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 359168 152003661 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359168 76944995 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359296 75058666 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 359424 508689574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 359424 278665432 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 359424 142622404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359424 71582577 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359552 71039827 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 359680 136043028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359680 69569166 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359808 66473862 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 359936 230024142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 359936 116810692 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 359936 59378021 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360064 57432671 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 360192 113213450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360192 56257321 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360320 56956129 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 344064 (MobiusHarmonicTree.branch 9830611264 mobiusHarmonicBlock042 mobiusHarmonicBlock043) = true := Helfgott.combined

#print axioms solution
