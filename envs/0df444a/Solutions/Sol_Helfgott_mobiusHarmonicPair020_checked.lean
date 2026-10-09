-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair020_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:05:37.513203+00:00
-- url     : https://prove2.me/submissions/b65c7f54-42a4-4741-8997-abf20852acdd

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327680 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327744 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 32345495 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327808 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327872 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 36410422 d11 d12
private def d6 : MobiusHarmonicTree := .branch 68755917 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327936 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328000 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 39890422 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328064 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328128 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 40932379 d18 d19
private def d13 : MobiusHarmonicTree := .branch 80822801 d14 d17
private def d5 : MobiusHarmonicTree := .branch 149578718 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328192 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328256 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 35807701 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328320 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328384 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 35096239 d26 d27
private def d21 : MobiusHarmonicTree := .branch 70903940 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328448 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328512 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 31816461 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328576 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328640 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 28468954 d33 d34
private def d28 : MobiusHarmonicTree := .branch 60285415 d29 d32
private def d20 : MobiusHarmonicTree := .branch 131189355 d21 d28
private def d4 : MobiusHarmonicTree := .branch 280768073 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328704 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328768 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 24658839 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328832 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328896 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 26354825 d42 d43
private def d37 : MobiusHarmonicTree := .branch 51013664 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 328960 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329024 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 27156209 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329088 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329152 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 30475366 d49 d50
private def d44 : MobiusHarmonicTree := .branch 57631575 d45 d48
private def d36 : MobiusHarmonicTree := .branch 108645239 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329216 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329280 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 28507669 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329344 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329408 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 29944702 d57 d58
private def d52 : MobiusHarmonicTree := .branch 58452371 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329472 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329536 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 28006204 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329600 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329664 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 27094400 d64 d65
private def d59 : MobiusHarmonicTree := .branch 55100604 d60 d63
private def d51 : MobiusHarmonicTree := .branch 113552975 d52 d59
private def d35 : MobiusHarmonicTree := .branch 222198214 d36 d51
private def d3 : MobiusHarmonicTree := .branch 502966287 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329728 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329792 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 28663615 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329856 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329920 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 29243488 d74 d75
private def d69 : MobiusHarmonicTree := .branch 57907103 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 329984 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330048 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 33249598 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330112 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330176 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 35026930 d81 d82
private def d76 : MobiusHarmonicTree := .branch 68276528 d77 d80
private def d68 : MobiusHarmonicTree := .branch 126183631 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330240 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330304 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 38966967 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330368 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330432 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 42989243 d89 d90
private def d84 : MobiusHarmonicTree := .branch 81956210 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330496 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330560 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 44279378 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330624 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330688 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 51069290 d96 d97
private def d91 : MobiusHarmonicTree := .branch 95348668 d92 d95
private def d83 : MobiusHarmonicTree := .branch 177304878 d84 d91
private def d67 : MobiusHarmonicTree := .branch 303488509 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330752 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330816 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 53123298 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330880 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 330944 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 52991125 d105 d106
private def d100 : MobiusHarmonicTree := .branch 106114423 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331008 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331072 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 47854022 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331136 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331200 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 45474072 d112 d113
private def d107 : MobiusHarmonicTree := .branch 93328094 d108 d111
private def d99 : MobiusHarmonicTree := .branch 199442517 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331264 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331328 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 50041162 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331392 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331456 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 49273747 d120 d121
private def d115 : MobiusHarmonicTree := .branch 99314909 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331520 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331584 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 53253463 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331648 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331712 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 52042455 d127 d128
private def d122 : MobiusHarmonicTree := .branch 105295918 d123 d126
private def d114 : MobiusHarmonicTree := .branch 204610827 d115 d122
private def d98 : MobiusHarmonicTree := .branch 404053344 d99 d114
private def d66 : MobiusHarmonicTree := .branch 707541853 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1210508140 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331776 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331840 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 47459844 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331904 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 331968 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 46477398 d138 d139
private def d133 : MobiusHarmonicTree := .branch 93937242 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332032 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332096 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 47218427 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332160 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332224 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 49518031 d145 d146
private def d140 : MobiusHarmonicTree := .branch 96736458 d141 d144
private def d132 : MobiusHarmonicTree := .branch 190673700 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332288 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332352 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 49282107 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332416 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332480 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 51380705 d153 d154
private def d148 : MobiusHarmonicTree := .branch 100662812 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332544 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332608 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 48306412 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332672 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332736 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 42316146 d160 d161
private def d155 : MobiusHarmonicTree := .branch 90622558 d156 d159
private def d147 : MobiusHarmonicTree := .branch 191285370 d148 d155
private def d131 : MobiusHarmonicTree := .branch 381959070 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332800 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332864 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 37877386 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332928 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 332992 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 40096983 d169 d170
private def d164 : MobiusHarmonicTree := .branch 77974369 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333056 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333120 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 43912349 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333184 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333248 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 41353764 d176 d177
private def d171 : MobiusHarmonicTree := .branch 85266113 d172 d175
private def d163 : MobiusHarmonicTree := .branch 163240482 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333312 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333376 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 40833984 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333440 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333504 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 43585713 d184 d185
private def d179 : MobiusHarmonicTree := .branch 84419697 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333568 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333632 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 43595987 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333696 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333760 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 45080343 d191 d192
private def d186 : MobiusHarmonicTree := .branch 88676330 d187 d190
private def d178 : MobiusHarmonicTree := .branch 173096027 d179 d186
private def d162 : MobiusHarmonicTree := .branch 336336509 d163 d178
private def d130 : MobiusHarmonicTree := .branch 718295579 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333824 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333888 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 48971608 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 333952 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334016 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 47054944 d201 d202
private def d196 : MobiusHarmonicTree := .branch 96026552 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334080 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334144 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 46491943 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334208 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334272 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 47844390 d208 d209
private def d203 : MobiusHarmonicTree := .branch 94336333 d204 d207
private def d195 : MobiusHarmonicTree := .branch 190362885 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334336 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334400 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 49632200 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334464 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334528 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 47619494 d216 d217
private def d211 : MobiusHarmonicTree := .branch 97251694 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334592 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334656 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 47834345 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334720 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334784 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 48989959 d223 d224
private def d218 : MobiusHarmonicTree := .branch 96824304 d219 d222
private def d210 : MobiusHarmonicTree := .branch 194075998 d211 d218
private def d194 : MobiusHarmonicTree := .branch 384438883 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334848 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334912 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 44098466 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 334976 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335040 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 44549819 d232 d233
private def d227 : MobiusHarmonicTree := .branch 88648285 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335104 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335168 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 50485321 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335232 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335296 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 49374456 d239 d240
private def d234 : MobiusHarmonicTree := .branch 99859777 d235 d238
private def d226 : MobiusHarmonicTree := .branch 188508062 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335360 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335424 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 50398849 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335488 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335552 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 53029181 d247 d248
private def d242 : MobiusHarmonicTree := .branch 103428030 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335616 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335680 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 56139705 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335744 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock040 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335808 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 54656491 d254 d255
private def d249 : MobiusHarmonicTree := .branch 110796196 d250 d253
private def d241 : MobiusHarmonicTree := .branch 214224226 d242 d249
private def d225 : MobiusHarmonicTree := .branch 402732288 d226 d241
private def d193 : MobiusHarmonicTree := .branch 787171171 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1505466750 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2715974890 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335872 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 335936 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 56362148 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336000 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336064 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 56295850 d266 d267
private def d261 : MobiusHarmonicTree := .branch 112657998 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336128 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336192 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 61280573 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336256 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336320 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 64168168 d273 d274
private def d268 : MobiusHarmonicTree := .branch 125448741 d269 d272
private def d260 : MobiusHarmonicTree := .branch 238106739 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336384 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336448 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 62758785 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336512 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336576 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 63997540 d281 d282
private def d276 : MobiusHarmonicTree := .branch 126756325 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336640 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336704 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 64977101 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336768 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336832 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 69298829 d288 d289
private def d283 : MobiusHarmonicTree := .branch 134275930 d284 d287
private def d275 : MobiusHarmonicTree := .branch 261032255 d276 d283
private def d259 : MobiusHarmonicTree := .branch 499138994 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336896 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 336960 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 65277985 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337024 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337088 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 67136845 d297 d298
private def d292 : MobiusHarmonicTree := .branch 132414830 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337152 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337216 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 68914357 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337280 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337344 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 70749859 d304 d305
private def d299 : MobiusHarmonicTree := .branch 139664216 d300 d303
private def d291 : MobiusHarmonicTree := .branch 272079046 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337408 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337472 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 69434152 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337536 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337600 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 72085316 d312 d313
private def d307 : MobiusHarmonicTree := .branch 141519468 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337664 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337728 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 73296013 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337792 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337856 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 69636248 d319 d320
private def d314 : MobiusHarmonicTree := .branch 142932261 d315 d318
private def d306 : MobiusHarmonicTree := .branch 284451729 d307 d314
private def d290 : MobiusHarmonicTree := .branch 556530775 d291 d306
private def d258 : MobiusHarmonicTree := .branch 1055669769 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337920 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 337984 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 73006470 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338048 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338112 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 73354407 d329 d330
private def d324 : MobiusHarmonicTree := .branch 146360877 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338176 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338240 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 79088776 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338304 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338368 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 85046534 d336 d337
private def d331 : MobiusHarmonicTree := .branch 164135310 d332 d335
private def d323 : MobiusHarmonicTree := .branch 310496187 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338432 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338496 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 88459156 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338560 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338624 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 88591209 d344 d345
private def d339 : MobiusHarmonicTree := .branch 177050365 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338688 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338752 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 83503820 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338816 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338880 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 82303686 d351 d352
private def d346 : MobiusHarmonicTree := .branch 165807506 d347 d350
private def d338 : MobiusHarmonicTree := .branch 342857871 d339 d346
private def d322 : MobiusHarmonicTree := .branch 653354058 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 338944 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339008 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 79284585 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339072 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339136 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 77570778 d360 d361
private def d355 : MobiusHarmonicTree := .branch 156855363 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339200 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339264 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 77842249 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339328 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339392 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 73269644 d367 d368
private def d362 : MobiusHarmonicTree := .branch 151111893 d363 d366
private def d354 : MobiusHarmonicTree := .branch 307967256 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339456 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339520 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 67707705 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339584 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339648 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 66092207 d375 d376
private def d370 : MobiusHarmonicTree := .branch 133799912 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339712 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339776 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 63412543 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339840 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339904 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 61135218 d382 d383
private def d377 : MobiusHarmonicTree := .branch 124547761 d378 d381
private def d369 : MobiusHarmonicTree := .branch 258347673 d370 d377
private def d353 : MobiusHarmonicTree := .branch 566314929 d354 d369
private def d321 : MobiusHarmonicTree := .branch 1219668987 d322 d353
private def d257 : MobiusHarmonicTree := .branch 2275338756 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 339968 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340032 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 58697479 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340096 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340160 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 60733285 d393 d394
private def d388 : MobiusHarmonicTree := .branch 119430764 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340224 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340288 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 60839726 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340352 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340416 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 61709841 d400 d401
private def d395 : MobiusHarmonicTree := .branch 122549567 d396 d399
private def d387 : MobiusHarmonicTree := .branch 241980331 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340480 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340544 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 58233647 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340608 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340672 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 59996137 d408 d409
private def d403 : MobiusHarmonicTree := .branch 118229784 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340736 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340800 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 59495434 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340864 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340928 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 64136525 d415 d416
private def d410 : MobiusHarmonicTree := .branch 123631959 d411 d414
private def d402 : MobiusHarmonicTree := .branch 241861743 d403 d410
private def d386 : MobiusHarmonicTree := .branch 483842074 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 340992 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341056 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 68308662 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341120 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341184 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 64490370 d424 d425
private def d419 : MobiusHarmonicTree := .branch 132799032 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341248 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341312 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 66976911 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341376 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341440 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 65226780 d431 d432
private def d426 : MobiusHarmonicTree := .branch 132203691 d427 d430
private def d418 : MobiusHarmonicTree := .branch 265002723 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341504 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341568 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 68554474 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341632 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341696 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 71233024 d439 d440
private def d434 : MobiusHarmonicTree := .branch 139787498 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341760 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341824 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 73306911 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341888 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 341952 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 70931163 d446 d447
private def d441 : MobiusHarmonicTree := .branch 144238074 d442 d445
private def d433 : MobiusHarmonicTree := .branch 284025572 d434 d441
private def d417 : MobiusHarmonicTree := .branch 549028295 d418 d433
private def d385 : MobiusHarmonicTree := .branch 1032870369 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342016 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342080 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 70314138 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342144 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342208 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 70626793 d456 d457
private def d451 : MobiusHarmonicTree := .branch 140940931 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342272 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342336 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 73477590 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342400 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342464 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 74326390 d463 d464
private def d458 : MobiusHarmonicTree := .branch 147803980 d459 d462
private def d450 : MobiusHarmonicTree := .branch 288744911 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342528 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342592 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 72894348 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342656 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342720 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 76286803 d471 d472
private def d466 : MobiusHarmonicTree := .branch 149181151 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342784 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342848 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 78273974 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342912 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 342976 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 73297039 d478 d479
private def d473 : MobiusHarmonicTree := .branch 151571013 d474 d477
private def d465 : MobiusHarmonicTree := .branch 300752164 d466 d473
private def d449 : MobiusHarmonicTree := .branch 589497075 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343040 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343104 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 70818405 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343168 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343232 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 71461929 d487 d488
private def d482 : MobiusHarmonicTree := .branch 142280334 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343296 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343360 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 70101570 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343424 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343488 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 66436279 d494 d495
private def d489 : MobiusHarmonicTree := .branch 136537849 d490 d493
private def d481 : MobiusHarmonicTree := .branch 278818183 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343552 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343616 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 69941347 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343680 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343744 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 72429189 d502 d503
private def d497 : MobiusHarmonicTree := .branch 142370536 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343808 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343872 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 71422217 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 343936 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock041 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 344000 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 70453714 d509 d510
private def d504 : MobiusHarmonicTree := .branch 141875931 d505 d508
private def d496 : MobiusHarmonicTree := .branch 284246467 d497 d504
private def d480 : MobiusHarmonicTree := .branch 563064650 d481 d496
private def d448 : MobiusHarmonicTree := .branch 1152561725 d449 d480
private def d384 : MobiusHarmonicTree := .branch 2185432094 d385 d448
private def d256 : MobiusHarmonicTree := .branch 4460770850 d257 d384
private def d0 : MobiusHarmonicTree := .branch 7176745740 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 327680 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 327680 7176745740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 327680 2715974890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 327680 1210508140 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 327680 502966287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 327680 280768073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 327680 149578718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 327680 68755917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327680 32345495 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327808 36410422 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 327936 80822801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327936 39890422 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328064 40932379 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 328192 131189355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 328192 70903940 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328192 35807701 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328320 35096239 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 328448 60285415 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328448 31816461 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328576 28468954 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 328704 222198214 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 328704 108645239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 328704 51013664 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328704 24658839 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328832 26354825 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 328960 57631575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 328960 27156209 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329088 30475366 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 329216 113552975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 329216 58452371 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329216 28507669 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329344 29944702 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 329472 55100604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329472 28006204 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329600 27094400 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 329728 707541853 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 329728 303488509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 329728 126183631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 329728 57907103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329728 28663615 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329856 29243488 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 329984 68276528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 329984 33249598 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 330112 35026930 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 330240 177304878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 330240 81956210 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 330240 38966967 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 330368 42989243 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 330496 95348668 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 330496 44279378 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 330624 51069290 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 330752 404053344 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 330752 199442517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 330752 106114423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 330752 53123298 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 330880 52991125 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 331008 93328094 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331008 47854022 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331136 45474072 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 331264 204610827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 331264 99314909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331264 50041162 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331392 49273747 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 331520 105295918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331520 53253463 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331648 52042455 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 331776 1505466750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 331776 718295579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 331776 381959070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 331776 190673700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 331776 93937242 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331776 47459844 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 331904 46477398 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 332032 96736458 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332032 47218427 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332160 49518031 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 332288 191285370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 332288 100662812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332288 49282107 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332416 51380705 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 332544 90622558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332544 48306412 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332672 42316146 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 332800 336336509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 332800 163240482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 332800 77974369 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332800 37877386 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 332928 40096983 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 333056 85266113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333056 43912349 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333184 41353764 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 333312 173096027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 333312 84419697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333312 40833984 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333440 43585713 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 333568 88676330 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333568 43595987 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333696 45080343 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 333824 787171171 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 333824 384438883 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 333824 190362885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 333824 96026552 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333824 48971608 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 333952 47054944 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 334080 94336333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334080 46491943 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334208 47844390 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 334336 194075998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 334336 97251694 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334336 49632200 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334464 47619494 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 334592 96824304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334592 47834345 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334720 48989959 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 334848 402732288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 334848 188508062 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 334848 88648285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334848 44098466 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 334976 44549819 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 335104 99859777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 335104 50485321 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 335232 49374456 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 335360 214224226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 335360 103428030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 335360 50398849 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 335488 53029181 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 335616 110796196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 335616 56139705 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 335744 54656491 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 335872 4460770850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 335872 2275338756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 335872 1055669769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 335872 499138994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 335872 238106739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 335872 112657998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 335872 56362148 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336000 56295850 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 336128 125448741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336128 61280573 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336256 64168168 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 336384 261032255 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 336384 126756325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336384 62758785 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336512 63997540 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 336640 134275930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336640 64977101 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336768 69298829 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 336896 556530775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 336896 272079046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 336896 132414830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 336896 65277985 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337024 67136845 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 337152 139664216 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337152 68914357 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337280 70749859 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 337408 284451729 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 337408 141519468 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337408 69434152 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337536 72085316 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 337664 142932261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337664 73296013 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337792 69636248 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 337920 1219668987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 337920 653354058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 337920 310496187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 337920 146360877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 337920 73006470 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338048 73354407 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 338176 164135310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338176 79088776 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338304 85046534 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 338432 342857871 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 338432 177050365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338432 88459156 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338560 88591209 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 338688 165807506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338688 83503820 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338816 82303686 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 338944 566314929 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 338944 307967256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 338944 156855363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 338944 79284585 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339072 77570778 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 339200 151111893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339200 77842249 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339328 73269644 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 339456 258347673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 339456 133799912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339456 67707705 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339584 66092207 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 339712 124547761 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339712 63412543 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339840 61135218 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 339968 2185432094 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 339968 1032870369 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 339968 483842074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 339968 241980331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 339968 119430764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 339968 58697479 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340096 60733285 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 340224 122549567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340224 60839726 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340352 61709841 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 340480 241861743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 340480 118229784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340480 58233647 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340608 59996137 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 340736 123631959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340736 59495434 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340864 64136525 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 340992 549028295 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 340992 265002723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 340992 132799032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 340992 68308662 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 341120 64490370 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 341248 132203691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 341248 66976911 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 341376 65226780 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 341504 284025572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 341504 139787498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 341504 68554474 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 341632 71233024 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 341760 144238074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 341760 73306911 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 341888 70931163 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 342016 1152561725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 342016 589497075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 342016 288744911 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 342016 140940931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342016 70314138 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342144 70626793 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 342272 147803980 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342272 73477590 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342400 74326390 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 342528 300752164 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 342528 149181151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342528 72894348 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342656 76286803 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 342784 151571013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342784 78273974 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 342912 73297039 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 343040 563064650 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 343040 278818183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 343040 142280334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343040 70818405 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343168 71461929 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 343296 136537849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343296 70101570 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343424 66436279 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 343552 284246467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 343552 142370536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343552 69941347 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343680 72429189 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 343808 141875931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343808 71422217 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 343936 70453714 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 327680 (MobiusHarmonicTree.branch 7176745740 mobiusHarmonicBlock040 mobiusHarmonicBlock041) = true := Helfgott.combined

#print axioms solution
