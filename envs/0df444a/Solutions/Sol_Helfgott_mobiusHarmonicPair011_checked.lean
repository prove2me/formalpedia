-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair011_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:32:24.805994+00:00
-- url     : https://prove2.me/submissions/5b138c40-36a8-4512-8d74-81e61b771933

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180224 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180288 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 44373844 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180352 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180416 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 47146219 d11 d12
private def d6 : MobiusHarmonicTree := .branch 91520063 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180480 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180544 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 51921437 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180608 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180672 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 47025009 d18 d19
private def d13 : MobiusHarmonicTree := .branch 98946446 d14 d17
private def d5 : MobiusHarmonicTree := .branch 190466509 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180736 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180800 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 48191297 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180864 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180928 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 49340295 d26 d27
private def d21 : MobiusHarmonicTree := .branch 97531592 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180992 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181056 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 51056093 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181120 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181184 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 51782264 d33 d34
private def d28 : MobiusHarmonicTree := .branch 102838357 d29 d32
private def d20 : MobiusHarmonicTree := .branch 200369949 d21 d28
private def d4 : MobiusHarmonicTree := .branch 390836458 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181248 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181312 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 50884664 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181376 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181440 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 54012735 d42 d43
private def d37 : MobiusHarmonicTree := .branch 104897399 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181504 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181568 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 48004419 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181632 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181696 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 44409514 d49 d50
private def d44 : MobiusHarmonicTree := .branch 92413933 d45 d48
private def d36 : MobiusHarmonicTree := .branch 197311332 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181760 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181824 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 40049533 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181888 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 181952 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 37312183 d57 d58
private def d52 : MobiusHarmonicTree := .branch 77361716 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182016 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182080 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 38313399 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182144 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182208 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 30048432 d64 d65
private def d59 : MobiusHarmonicTree := .branch 68361831 d60 d63
private def d51 : MobiusHarmonicTree := .branch 145723547 d52 d59
private def d35 : MobiusHarmonicTree := .branch 343034879 d36 d51
private def d3 : MobiusHarmonicTree := .branch 733871337 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182272 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182336 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 36970150 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182400 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182464 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 35530600 d74 d75
private def d69 : MobiusHarmonicTree := .branch 72500750 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182528 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182592 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 26053262 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182656 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182720 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 24758836 d81 d82
private def d76 : MobiusHarmonicTree := .branch 50812098 d77 d80
private def d68 : MobiusHarmonicTree := .branch 123312848 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182784 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182848 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 40191592 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182912 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 182976 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 43645333 d89 d90
private def d84 : MobiusHarmonicTree := .branch 83836925 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183040 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183104 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 41861447 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183168 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183232 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 45571024 d96 d97
private def d91 : MobiusHarmonicTree := .branch 87432471 d92 d95
private def d83 : MobiusHarmonicTree := .branch 171269396 d84 d91
private def d67 : MobiusHarmonicTree := .branch 294582244 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183296 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183360 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 32903200 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183424 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183488 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 26721866 d105 d106
private def d100 : MobiusHarmonicTree := .branch 59625066 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183552 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183616 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 21223547 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183680 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183744 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 24457707 d112 d113
private def d107 : MobiusHarmonicTree := .branch 45681254 d108 d111
private def d99 : MobiusHarmonicTree := .branch 105306320 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183808 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183872 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 22303529 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 183936 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184000 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 20386574 d120 d121
private def d115 : MobiusHarmonicTree := .branch 42690103 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184064 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184128 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 16179075 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184192 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184256 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 17584490 d127 d128
private def d122 : MobiusHarmonicTree := .branch 33763565 d123 d126
private def d114 : MobiusHarmonicTree := .branch 76453668 d115 d122
private def d98 : MobiusHarmonicTree := .branch 181759988 d99 d114
private def d66 : MobiusHarmonicTree := .branch 476342232 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1210213569 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184320 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184384 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 19621000 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184448 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184512 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 29066220 d138 d139
private def d133 : MobiusHarmonicTree := .branch 48687220 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184576 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184640 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 29624829 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184704 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184768 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 37987768 d145 d146
private def d140 : MobiusHarmonicTree := .branch 67612597 d141 d144
private def d132 : MobiusHarmonicTree := .branch 116299817 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184832 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184896 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 37139981 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 184960 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185024 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 39784361 d153 d154
private def d148 : MobiusHarmonicTree := .branch 76924342 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185088 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185152 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 37239980 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185216 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185280 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 33932508 d160 d161
private def d155 : MobiusHarmonicTree := .branch 71172488 d156 d159
private def d147 : MobiusHarmonicTree := .branch 148096830 d148 d155
private def d131 : MobiusHarmonicTree := .branch 264396647 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185344 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185408 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 31638563 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185472 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185536 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 30274662 d169 d170
private def d164 : MobiusHarmonicTree := .branch 61913225 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185600 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185664 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 25751630 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185728 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185792 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 18149977 d176 d177
private def d171 : MobiusHarmonicTree := .branch 43901607 d172 d175
private def d163 : MobiusHarmonicTree := .branch 105814832 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185856 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185920 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 16512439 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 185984 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186048 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 17850589 d184 d185
private def d179 : MobiusHarmonicTree := .branch 34363028 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186112 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186176 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 16850106 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186240 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186304 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 17841750 d191 d192
private def d186 : MobiusHarmonicTree := .branch 34691856 d187 d190
private def d178 : MobiusHarmonicTree := .branch 69054884 d179 d186
private def d162 : MobiusHarmonicTree := .branch 174869716 d163 d178
private def d130 : MobiusHarmonicTree := .branch 439266363 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186368 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186432 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 24469817 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186496 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186560 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 34224781 d201 d202
private def d196 : MobiusHarmonicTree := .branch 58694598 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186624 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186688 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 34009479 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186752 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186816 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 28642887 d208 d209
private def d203 : MobiusHarmonicTree := .branch 62652366 d204 d207
private def d195 : MobiusHarmonicTree := .branch 121346964 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186880 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 186944 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 33245048 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187008 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187072 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 36413974 d216 d217
private def d211 : MobiusHarmonicTree := .branch 69659022 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187136 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187200 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 29092235 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187264 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187328 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 24685010 d223 d224
private def d218 : MobiusHarmonicTree := .branch 53777245 d219 d222
private def d210 : MobiusHarmonicTree := .branch 123436267 d211 d218
private def d194 : MobiusHarmonicTree := .branch 244783231 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187392 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187456 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 14275464 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187520 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187584 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 12234883 d232 d233
private def d227 : MobiusHarmonicTree := .branch 26510347 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187648 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187712 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 9195077 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187776 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187840 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 17333192 d239 d240
private def d234 : MobiusHarmonicTree := .branch 26528269 d235 d238
private def d226 : MobiusHarmonicTree := .branch 53038616 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187904 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 187968 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 19944811 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188032 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188096 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 27347211 d247 d248
private def d242 : MobiusHarmonicTree := .branch 47292022 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188160 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188224 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 32439830 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188288 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock022 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188352 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 29042192 d254 d255
private def d249 : MobiusHarmonicTree := .branch 61482022 d250 d253
private def d241 : MobiusHarmonicTree := .branch 108774044 d242 d249
private def d225 : MobiusHarmonicTree := .branch 161812660 d226 d241
private def d193 : MobiusHarmonicTree := .branch 406595891 d194 d225
private def d129 : MobiusHarmonicTree := .branch 845862254 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2056075823 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188416 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188480 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 23280685 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188544 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188608 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 28625355 d266 d267
private def d261 : MobiusHarmonicTree := .branch 51906040 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188672 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188736 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 26873590 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188800 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188864 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 26538046 d273 d274
private def d268 : MobiusHarmonicTree := .branch 53411636 d269 d272
private def d260 : MobiusHarmonicTree := .branch 105317676 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188928 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 188992 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 25678351 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189056 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189120 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 35918781 d281 d282
private def d276 : MobiusHarmonicTree := .branch 61597132 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189184 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189248 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 34103446 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189312 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189376 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 36884718 d288 d289
private def d283 : MobiusHarmonicTree := .branch 70988164 d284 d287
private def d275 : MobiusHarmonicTree := .branch 132585296 d276 d283
private def d259 : MobiusHarmonicTree := .branch 237902972 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189440 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189504 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 31334939 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189568 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189632 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 28465996 d297 d298
private def d292 : MobiusHarmonicTree := .branch 59800935 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189696 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189760 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 22144300 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189824 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189888 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 19685563 d304 d305
private def d299 : MobiusHarmonicTree := .branch 41829863 d300 d303
private def d291 : MobiusHarmonicTree := .branch 101630798 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 189952 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190016 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 20282080 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190080 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190144 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 22604030 d312 d313
private def d307 : MobiusHarmonicTree := .branch 42886110 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190208 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190272 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 29463019 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190336 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190400 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 27043007 d319 d320
private def d314 : MobiusHarmonicTree := .branch 56506026 d315 d318
private def d306 : MobiusHarmonicTree := .branch 99392136 d307 d314
private def d290 : MobiusHarmonicTree := .branch 201022934 d291 d306
private def d258 : MobiusHarmonicTree := .branch 438925906 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190464 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190528 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 38839281 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190592 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190656 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 38598266 d329 d330
private def d324 : MobiusHarmonicTree := .branch 77437547 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190720 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190784 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 36423628 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190848 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190912 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 37362613 d336 d337
private def d331 : MobiusHarmonicTree := .branch 73786241 d332 d335
private def d323 : MobiusHarmonicTree := .branch 151223788 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 190976 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191040 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 47094948 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191104 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191168 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 49955803 d344 d345
private def d339 : MobiusHarmonicTree := .branch 97050751 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191232 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191296 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 51883025 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191360 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191424 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 55614626 d351 d352
private def d346 : MobiusHarmonicTree := .branch 107497651 d347 d350
private def d338 : MobiusHarmonicTree := .branch 204548402 d339 d346
private def d322 : MobiusHarmonicTree := .branch 355772190 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191488 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191552 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 55822859 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191616 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191680 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 60152705 d360 d361
private def d355 : MobiusHarmonicTree := .branch 115975564 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191744 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191808 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 59288952 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191872 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 191936 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 59957903 d367 d368
private def d362 : MobiusHarmonicTree := .branch 119246855 d363 d366
private def d354 : MobiusHarmonicTree := .branch 235222419 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192000 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192064 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 55222187 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192128 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192192 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 44092129 d375 d376
private def d370 : MobiusHarmonicTree := .branch 99314316 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192256 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192320 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 34536597 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192384 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192448 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 35380805 d382 d383
private def d377 : MobiusHarmonicTree := .branch 69917402 d378 d381
private def d369 : MobiusHarmonicTree := .branch 169231718 d370 d377
private def d353 : MobiusHarmonicTree := .branch 404454137 d354 d369
private def d321 : MobiusHarmonicTree := .branch 760226327 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1199152233 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192512 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192576 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 35316452 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192640 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192704 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 34918756 d393 d394
private def d388 : MobiusHarmonicTree := .branch 70235208 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192768 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192832 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 31297201 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192896 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192960 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 26186801 d400 d401
private def d395 : MobiusHarmonicTree := .branch 57484002 d396 d399
private def d387 : MobiusHarmonicTree := .branch 127719210 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193024 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193088 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 28375923 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193152 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193216 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 21002845 d408 d409
private def d403 : MobiusHarmonicTree := .branch 49378768 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193280 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193344 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 16028657 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193408 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193472 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 12115628 d415 d416
private def d410 : MobiusHarmonicTree := .branch 28144285 d411 d414
private def d402 : MobiusHarmonicTree := .branch 77523053 d403 d410
private def d386 : MobiusHarmonicTree := .branch 205242263 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193536 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193600 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 12102796 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193664 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193728 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 15211899 d424 d425
private def d419 : MobiusHarmonicTree := .branch 27314695 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193792 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193856 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 13443019 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193920 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 193984 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 11944333 d431 d432
private def d426 : MobiusHarmonicTree := .branch 25387352 d427 d430
private def d418 : MobiusHarmonicTree := .branch 52702047 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194048 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194112 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 9062466 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194176 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194240 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 3366920 d439 d440
private def d434 : MobiusHarmonicTree := .branch 12429386 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194304 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194368 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 8833355 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194432 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194496 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 10972329 d446 d447
private def d441 : MobiusHarmonicTree := .branch 19805684 d442 d445
private def d433 : MobiusHarmonicTree := .branch 32235070 d434 d441
private def d417 : MobiusHarmonicTree := .branch 84937117 d418 d433
private def d385 : MobiusHarmonicTree := .branch 290179380 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194560 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194624 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 10543387 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194688 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194752 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 5976939 d456 d457
private def d451 : MobiusHarmonicTree := .branch 16520326 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194816 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194880 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 3006975 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 194944 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195008 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 3696980 d463 d464
private def d458 : MobiusHarmonicTree := .branch 6703955 d459 d462
private def d450 : MobiusHarmonicTree := .branch 23224281 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195072 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195136 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 11525255 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195200 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195264 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 10529449 d471 d472
private def d466 : MobiusHarmonicTree := .branch 22054704 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195328 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195392 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 5404956 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195456 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195520 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 3273360 d478 d479
private def d473 : MobiusHarmonicTree := .branch 8678316 d474 d477
private def d465 : MobiusHarmonicTree := .branch 30733020 d466 d473
private def d449 : MobiusHarmonicTree := .branch 53957301 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195584 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195648 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 2621964 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195712 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195776 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 3360955 d487 d488
private def d482 : MobiusHarmonicTree := .branch 5982919 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195840 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195904 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 2613629 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 195968 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196032 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 4504140 d494 d495
private def d489 : MobiusHarmonicTree := .branch 7117769 d490 d493
private def d481 : MobiusHarmonicTree := .branch 13100688 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196096 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196160 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 4328004 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196224 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196288 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 1385904 d502 d503
private def d497 : MobiusHarmonicTree := .branch 5713908 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196352 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196416 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 5935962 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196480 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock023 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196544 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 3302548 d509 d510
private def d504 : MobiusHarmonicTree := .branch 9238510 d505 d508
private def d496 : MobiusHarmonicTree := .branch 14952418 d497 d504
private def d480 : MobiusHarmonicTree := .branch 28053106 d481 d496
private def d448 : MobiusHarmonicTree := .branch 82010407 d449 d480
private def d384 : MobiusHarmonicTree := .branch 372189787 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1571342020 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3627417843 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 180224 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 180224 3627417843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 180224 2056075823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 180224 1210213569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 180224 733871337 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 180224 390836458 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 180224 190466509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 180224 91520063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180224 44373844 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180352 47146219 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 180480 98946446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180480 51921437 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180608 47025009 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 180736 200369949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 180736 97531592 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180736 48191297 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180864 49340295 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 180992 102838357 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180992 51056093 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 181120 51782264 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 181248 343034879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 181248 197311332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 181248 104897399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 181248 50884664 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 181376 54012735 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 181504 92413933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 181504 48004419 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 181632 44409514 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 181760 145723547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 181760 77361716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 181760 40049533 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 181888 37312183 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 182016 68361831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182016 38313399 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182144 30048432 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 182272 476342232 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 182272 294582244 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 182272 123312848 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 182272 72500750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182272 36970150 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182400 35530600 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 182528 50812098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182528 26053262 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182656 24758836 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 182784 171269396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 182784 83836925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182784 40191592 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 182912 43645333 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 183040 87432471 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183040 41861447 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183168 45571024 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 183296 181759988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 183296 105306320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 183296 59625066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183296 32903200 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183424 26721866 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 183552 45681254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183552 21223547 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183680 24457707 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 183808 76453668 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 183808 42690103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183808 22303529 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 183936 20386574 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 184064 33763565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184064 16179075 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184192 17584490 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 184320 845862254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 184320 439266363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 184320 264396647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 184320 116299817 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 184320 48687220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184320 19621000 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184448 29066220 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 184576 67612597 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184576 29624829 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184704 37987768 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 184832 148096830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 184832 76924342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184832 37139981 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 184960 39784361 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 185088 71172488 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185088 37239980 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185216 33932508 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 185344 174869716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 185344 105814832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 185344 61913225 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185344 31638563 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185472 30274662 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 185600 43901607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185600 25751630 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185728 18149977 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 185856 69054884 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 185856 34363028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185856 16512439 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 185984 17850589 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 186112 34691856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 186112 16850106 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 186240 17841750 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 186368 406595891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 186368 244783231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 186368 121346964 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 186368 58694598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 186368 24469817 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 186496 34224781 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 186624 62652366 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 186624 34009479 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 186752 28642887 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 186880 123436267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 186880 69659022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 186880 33245048 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187008 36413974 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 187136 53777245 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187136 29092235 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187264 24685010 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 187392 161812660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 187392 53038616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 187392 26510347 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187392 14275464 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187520 12234883 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 187648 26528269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187648 9195077 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187776 17333192 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 187904 108774044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 187904 47292022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 187904 19944811 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188032 27347211 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 188160 61482022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188160 32439830 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188288 29042192 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 188416 1571342020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 188416 1199152233 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 188416 438925906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 188416 237902972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 188416 105317676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 188416 51906040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188416 23280685 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188544 28625355 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 188672 53411636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188672 26873590 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188800 26538046 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 188928 132585296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 188928 61597132 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 188928 25678351 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189056 35918781 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 189184 70988164 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189184 34103446 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189312 36884718 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 189440 201022934 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 189440 101630798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 189440 59800935 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189440 31334939 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189568 28465996 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 189696 41829863 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189696 22144300 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189824 19685563 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 189952 99392136 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 189952 42886110 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 189952 20282080 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190080 22604030 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 190208 56506026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190208 29463019 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190336 27043007 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 190464 760226327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 190464 355772190 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 190464 151223788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 190464 77437547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190464 38839281 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190592 38598266 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 190720 73786241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190720 36423628 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190848 37362613 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 190976 204548402 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 190976 97050751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 190976 47094948 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 191104 49955803 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 191232 107497651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 191232 51883025 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 191360 55614626 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 191488 404454137 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 191488 235222419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 191488 115975564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 191488 55822859 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 191616 60152705 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 191744 119246855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 191744 59288952 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 191872 59957903 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 192000 169231718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 192000 99314316 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192000 55222187 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192128 44092129 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 192256 69917402 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192256 34536597 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192384 35380805 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 192512 372189787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 192512 290179380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 192512 205242263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 192512 127719210 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 192512 70235208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192512 35316452 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192640 34918756 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 192768 57484002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192768 31297201 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 192896 26186801 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 193024 77523053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 193024 49378768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193024 28375923 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193152 21002845 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 193280 28144285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193280 16028657 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193408 12115628 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 193536 84937117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 193536 52702047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 193536 27314695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193536 12102796 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193664 15211899 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 193792 25387352 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193792 13443019 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 193920 11944333 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 194048 32235070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 194048 12429386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194048 9062466 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194176 3366920 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 194304 19805684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194304 8833355 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194432 10972329 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 194560 82010407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 194560 53957301 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 194560 23224281 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 194560 16520326 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194560 10543387 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194688 5976939 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 194816 6703955 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194816 3006975 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 194944 3696980 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 195072 30733020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 195072 22054704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195072 11525255 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195200 10529449 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 195328 8678316 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195328 5404956 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195456 3273360 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 195584 28053106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 195584 13100688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 195584 5982919 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195584 2621964 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195712 3360955 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 195840 7117769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195840 2613629 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 195968 4504140 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 196096 14952418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 196096 5713908 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196096 4328004 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196224 1385904 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 196352 9238510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196352 5935962 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196480 3302548 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 180224 (MobiusHarmonicTree.branch 3627417843 mobiusHarmonicBlock022 mobiusHarmonicBlock023) = true := Helfgott.combined

#print axioms solution
