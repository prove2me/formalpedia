-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair012_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:35:20.431628+00:00
-- url     : https://prove2.me/submissions/105a490e-89d2-4b9a-8466-06367abb1ce3

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196608 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196672 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 1881288 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196736 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196800 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 2042814 d11 d12
private def d6 : MobiusHarmonicTree := .branch 3924102 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196864 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196928 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 3655985 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 196992 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197056 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 4075021 d18 d19
private def d13 : MobiusHarmonicTree := .branch 7731006 d14 d17
private def d5 : MobiusHarmonicTree := .branch 11655108 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197120 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197184 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 5664905 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197248 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197312 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 2716689 d26 d27
private def d21 : MobiusHarmonicTree := .branch 8381594 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197376 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197440 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 1732147 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197504 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197568 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 4727586 d33 d34
private def d28 : MobiusHarmonicTree := .branch 6459733 d29 d32
private def d20 : MobiusHarmonicTree := .branch 14841327 d21 d28
private def d4 : MobiusHarmonicTree := .branch 26496435 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197632 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197696 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 2149829 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197760 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197824 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 2618296 d42 d43
private def d37 : MobiusHarmonicTree := .branch 4768125 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197888 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 197952 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 2389531 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198016 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198080 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 2110315 d49 d50
private def d44 : MobiusHarmonicTree := .branch 4499846 d45 d48
private def d36 : MobiusHarmonicTree := .branch 9267971 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198144 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198208 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 2467315 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198272 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198336 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 1694286 d57 d58
private def d52 : MobiusHarmonicTree := .branch 4161601 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198400 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198464 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 3103879 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198528 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198592 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 4642367 d64 d65
private def d59 : MobiusHarmonicTree := .branch 7746246 d60 d63
private def d51 : MobiusHarmonicTree := .branch 11907847 d52 d59
private def d35 : MobiusHarmonicTree := .branch 21175818 d36 d51
private def d3 : MobiusHarmonicTree := .branch 47672253 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198656 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198720 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 10089689 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198784 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198848 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 8076304 d74 d75
private def d69 : MobiusHarmonicTree := .branch 18165993 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198912 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 198976 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 18876275 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199040 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199104 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 14400175 d81 d82
private def d76 : MobiusHarmonicTree := .branch 33276450 d77 d80
private def d68 : MobiusHarmonicTree := .branch 51442443 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199168 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199232 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 9346314 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199296 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199360 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 3667096 d89 d90
private def d84 : MobiusHarmonicTree := .branch 13013410 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199424 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199488 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 4511460 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199552 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199616 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 2454904 d96 d97
private def d91 : MobiusHarmonicTree := .branch 6966364 d92 d95
private def d83 : MobiusHarmonicTree := .branch 19979774 d84 d91
private def d67 : MobiusHarmonicTree := .branch 71422217 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199680 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199744 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 3144397 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199808 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199872 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 3707129 d105 d106
private def d100 : MobiusHarmonicTree := .branch 6851526 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 199936 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200000 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 4905135 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200064 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200128 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 6755747 d112 d113
private def d107 : MobiusHarmonicTree := .branch 11660882 d108 d111
private def d99 : MobiusHarmonicTree := .branch 18512408 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200192 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200256 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 8838580 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200320 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200384 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 11308429 d120 d121
private def d115 : MobiusHarmonicTree := .branch 20147009 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200448 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200512 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 12204038 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200576 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200640 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 2572249 d127 d128
private def d122 : MobiusHarmonicTree := .branch 14776287 d123 d126
private def d114 : MobiusHarmonicTree := .branch 34923296 d115 d122
private def d98 : MobiusHarmonicTree := .branch 53435704 d99 d114
private def d66 : MobiusHarmonicTree := .branch 124857921 d67 d98
private def d2 : MobiusHarmonicTree := .branch 172530174 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200704 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200768 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 3197436 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200832 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200896 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 9990419 d138 d139
private def d133 : MobiusHarmonicTree := .branch 13187855 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 200960 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201024 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 12436336 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201088 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201152 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 12309258 d145 d146
private def d140 : MobiusHarmonicTree := .branch 24745594 d141 d144
private def d132 : MobiusHarmonicTree := .branch 37933449 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201216 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201280 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 9738002 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201344 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201408 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 15609684 d153 d154
private def d148 : MobiusHarmonicTree := .branch 25347686 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201472 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201536 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 9720730 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201600 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201664 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 6813445 d160 d161
private def d155 : MobiusHarmonicTree := .branch 16534175 d156 d159
private def d147 : MobiusHarmonicTree := .branch 41881861 d148 d155
private def d131 : MobiusHarmonicTree := .branch 79815310 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201728 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201792 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 2968564 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201856 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201920 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 4665188 d169 d170
private def d164 : MobiusHarmonicTree := .branch 7633752 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 201984 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202048 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 3707311 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202112 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202176 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 1825396 d176 d177
private def d171 : MobiusHarmonicTree := .branch 5532707 d172 d175
private def d163 : MobiusHarmonicTree := .branch 13166459 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202240 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202304 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 1665913 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202368 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202432 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 7068577 d184 d185
private def d179 : MobiusHarmonicTree := .branch 8734490 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202496 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202560 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 7513649 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202624 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202688 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 11406734 d191 d192
private def d186 : MobiusHarmonicTree := .branch 18920383 d187 d190
private def d178 : MobiusHarmonicTree := .branch 27654873 d179 d186
private def d162 : MobiusHarmonicTree := .branch 40821332 d163 d178
private def d130 : MobiusHarmonicTree := .branch 120636642 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202752 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202816 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 9861207 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202880 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 202944 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 9584086 d201 d202
private def d196 : MobiusHarmonicTree := .branch 19445293 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203008 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203072 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 11911636 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203136 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203200 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 22362065 d208 d209
private def d203 : MobiusHarmonicTree := .branch 34273701 d204 d207
private def d195 : MobiusHarmonicTree := .branch 53718994 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203264 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203328 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 20489596 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203392 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203456 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 18332760 d216 d217
private def d211 : MobiusHarmonicTree := .branch 38822356 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203520 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203584 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 24889503 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203648 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203712 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 23056517 d223 d224
private def d218 : MobiusHarmonicTree := .branch 47946020 d219 d222
private def d210 : MobiusHarmonicTree := .branch 86768376 d211 d218
private def d194 : MobiusHarmonicTree := .branch 140487370 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203776 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203840 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 27757139 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203904 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 203968 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 27641872 d232 d233
private def d227 : MobiusHarmonicTree := .branch 55399011 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204032 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204096 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 27379182 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204160 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204224 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 33526725 d239 d240
private def d234 : MobiusHarmonicTree := .branch 60905907 d235 d238
private def d226 : MobiusHarmonicTree := .branch 116304918 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204288 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204352 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 38057130 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204416 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204480 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 37289897 d247 d248
private def d242 : MobiusHarmonicTree := .branch 75347027 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204544 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204608 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 38228835 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204672 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock024 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204736 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 47490718 d254 d255
private def d249 : MobiusHarmonicTree := .branch 85719553 d250 d253
private def d241 : MobiusHarmonicTree := .branch 161066580 d242 d249
private def d225 : MobiusHarmonicTree := .branch 277371498 d226 d241
private def d193 : MobiusHarmonicTree := .branch 417858868 d194 d225
private def d129 : MobiusHarmonicTree := .branch 538495510 d130 d193
private def d1 : MobiusHarmonicTree := .branch 711025684 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204800 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204864 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 42198977 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204928 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 204992 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 36235770 d266 d267
private def d261 : MobiusHarmonicTree := .branch 78434747 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205056 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205120 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 30134151 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205184 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205248 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 27425441 d273 d274
private def d268 : MobiusHarmonicTree := .branch 57559592 d269 d272
private def d260 : MobiusHarmonicTree := .branch 135994339 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205312 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205376 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 23099518 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205440 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205504 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 12355476 d281 d282
private def d276 : MobiusHarmonicTree := .branch 35454994 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205568 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205632 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 10727964 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205696 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205760 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 17111968 d288 d289
private def d283 : MobiusHarmonicTree := .branch 27839932 d284 d287
private def d275 : MobiusHarmonicTree := .branch 63294926 d276 d283
private def d259 : MobiusHarmonicTree := .branch 199289265 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205824 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205888 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 17563004 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 205952 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206016 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 15013758 d297 d298
private def d292 : MobiusHarmonicTree := .branch 32576762 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206080 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206144 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 12694935 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206208 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206272 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 10127919 d304 d305
private def d299 : MobiusHarmonicTree := .branch 22822854 d300 d303
private def d291 : MobiusHarmonicTree := .branch 55399616 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206336 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206400 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 5044117 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206464 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206528 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 2314660 d312 d313
private def d307 : MobiusHarmonicTree := .branch 7358777 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206592 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206656 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 5463382 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206720 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206784 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 2069581 d319 d320
private def d314 : MobiusHarmonicTree := .branch 7532963 d315 d318
private def d306 : MobiusHarmonicTree := .branch 14891740 d307 d314
private def d290 : MobiusHarmonicTree := .branch 70291356 d291 d306
private def d258 : MobiusHarmonicTree := .branch 269580621 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206848 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206912 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 6079765 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 206976 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207040 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 5013398 d329 d330
private def d324 : MobiusHarmonicTree := .branch 11093163 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207104 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207168 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 8620847 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207232 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207296 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 15422053 d336 d337
private def d331 : MobiusHarmonicTree := .branch 24042900 d332 d335
private def d323 : MobiusHarmonicTree := .branch 35136063 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207360 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207424 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 18175390 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207488 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207552 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 27655337 d344 d345
private def d339 : MobiusHarmonicTree := .branch 45830727 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207616 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207680 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 30359393 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207744 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207808 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 28627315 d351 d352
private def d346 : MobiusHarmonicTree := .branch 58986708 d347 d350
private def d338 : MobiusHarmonicTree := .branch 104817435 d339 d346
private def d322 : MobiusHarmonicTree := .branch 139953498 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207872 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 207936 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 32986356 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208000 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208064 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 28174218 d360 d361
private def d355 : MobiusHarmonicTree := .branch 61160574 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208128 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208192 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 29689053 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208256 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208320 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 30948143 d367 d368
private def d362 : MobiusHarmonicTree := .branch 60637196 d363 d366
private def d354 : MobiusHarmonicTree := .branch 121797770 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208384 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208448 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 30098751 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208512 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208576 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 36092222 d375 d376
private def d370 : MobiusHarmonicTree := .branch 66190973 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208640 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208704 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 41029448 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208768 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208832 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 40132683 d382 d383
private def d377 : MobiusHarmonicTree := .branch 81162131 d378 d381
private def d369 : MobiusHarmonicTree := .branch 147353104 d370 d377
private def d353 : MobiusHarmonicTree := .branch 269150874 d354 d369
private def d321 : MobiusHarmonicTree := .branch 409104372 d322 d353
private def d257 : MobiusHarmonicTree := .branch 678684993 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208896 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 208960 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 41113360 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209024 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209088 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 41963630 d393 d394
private def d388 : MobiusHarmonicTree := .branch 83076990 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209152 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209216 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 38959442 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209280 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209344 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 48928818 d400 d401
private def d395 : MobiusHarmonicTree := .branch 87888260 d396 d399
private def d387 : MobiusHarmonicTree := .branch 170965250 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209408 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209472 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 46890004 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209536 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209600 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 42175876 d408 d409
private def d403 : MobiusHarmonicTree := .branch 89065880 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209664 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209728 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 40271712 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209792 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209856 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 38421802 d415 d416
private def d410 : MobiusHarmonicTree := .branch 78693514 d411 d414
private def d402 : MobiusHarmonicTree := .branch 167759394 d403 d410
private def d386 : MobiusHarmonicTree := .branch 338724644 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209920 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 209984 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 38478961 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210048 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210112 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 41929764 d424 d425
private def d419 : MobiusHarmonicTree := .branch 80408725 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210176 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210240 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 51364746 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210304 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210368 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 56468196 d431 d432
private def d426 : MobiusHarmonicTree := .branch 107832942 d427 d430
private def d418 : MobiusHarmonicTree := .branch 188241667 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210432 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210496 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 48405389 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210560 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210624 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 41467756 d439 d440
private def d434 : MobiusHarmonicTree := .branch 89873145 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210688 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210752 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 32725943 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210816 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210880 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 37769715 d446 d447
private def d441 : MobiusHarmonicTree := .branch 70495658 d442 d445
private def d433 : MobiusHarmonicTree := .branch 160368803 d434 d441
private def d417 : MobiusHarmonicTree := .branch 348610470 d418 d433
private def d385 : MobiusHarmonicTree := .branch 687335114 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 210944 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211008 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 40724145 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211072 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211136 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 39548080 d456 d457
private def d451 : MobiusHarmonicTree := .branch 80272225 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211200 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211264 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 42761846 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211328 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211392 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 39268715 d463 d464
private def d458 : MobiusHarmonicTree := .branch 82030561 d459 d462
private def d450 : MobiusHarmonicTree := .branch 162302786 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211456 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211520 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 34706345 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211584 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211648 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 36300786 d471 d472
private def d466 : MobiusHarmonicTree := .branch 71007131 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211712 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211776 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 36373443 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211840 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211904 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 39248995 d478 d479
private def d473 : MobiusHarmonicTree := .branch 75622438 d474 d477
private def d465 : MobiusHarmonicTree := .branch 146629569 d466 d473
private def d449 : MobiusHarmonicTree := .branch 308932355 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 211968 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212032 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 37098600 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212096 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212160 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 37928913 d487 d488
private def d482 : MobiusHarmonicTree := .branch 75027513 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212224 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212288 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 36526367 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212352 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212416 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 32120969 d494 d495
private def d489 : MobiusHarmonicTree := .branch 68647336 d490 d493
private def d481 : MobiusHarmonicTree := .branch 143674849 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212480 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212544 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 28935888 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212608 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212672 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 24258137 d502 d503
private def d497 : MobiusHarmonicTree := .branch 53194025 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212736 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212800 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 15785096 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212864 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock025 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212928 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 14272448 d509 d510
private def d504 : MobiusHarmonicTree := .branch 30057544 d505 d508
private def d496 : MobiusHarmonicTree := .branch 83251569 d497 d504
private def d480 : MobiusHarmonicTree := .branch 226926418 d481 d496
private def d448 : MobiusHarmonicTree := .branch 535858773 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1223193887 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1901878880 d257 d384
private def d0 : MobiusHarmonicTree := .branch 2612904564 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 196608 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 196608 2612904564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 196608 711025684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 196608 172530174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 196608 47672253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 196608 26496435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 196608 11655108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 196608 3924102 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196608 1881288 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196736 2042814 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 196864 7731006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196864 3655985 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 196992 4075021 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 197120 14841327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 197120 8381594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 197120 5664905 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 197248 2716689 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 197376 6459733 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 197376 1732147 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 197504 4727586 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 197632 21175818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 197632 9267971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 197632 4768125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 197632 2149829 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 197760 2618296 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 197888 4499846 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 197888 2389531 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198016 2110315 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 198144 11907847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 198144 4161601 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198144 2467315 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198272 1694286 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 198400 7746246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198400 3103879 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198528 4642367 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 198656 124857921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 198656 71422217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 198656 51442443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 198656 18165993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198656 10089689 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198784 8076304 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 198912 33276450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 198912 18876275 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199040 14400175 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 199168 19979774 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 199168 13013410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199168 9346314 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199296 3667096 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 199424 6966364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199424 4511460 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199552 2454904 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 199680 53435704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 199680 18512408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 199680 6851526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199680 3144397 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199808 3707129 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 199936 11660882 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 199936 4905135 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200064 6755747 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 200192 34923296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 200192 20147009 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200192 8838580 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200320 11308429 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 200448 14776287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200448 12204038 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200576 2572249 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 200704 538495510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 200704 120636642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 200704 79815310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 200704 37933449 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 200704 13187855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200704 3197436 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200832 9990419 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 200960 24745594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 200960 12436336 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201088 12309258 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 201216 41881861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 201216 25347686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201216 9738002 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201344 15609684 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 201472 16534175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201472 9720730 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201600 6813445 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 201728 40821332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 201728 13166459 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 201728 7633752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201728 2968564 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201856 4665188 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 201984 5532707 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 201984 3707311 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 202112 1825396 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 202240 27654873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 202240 8734490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 202240 1665913 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 202368 7068577 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 202496 18920383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 202496 7513649 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 202624 11406734 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 202752 417858868 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 202752 140487370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 202752 53718994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 202752 19445293 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 202752 9861207 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 202880 9584086 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 203008 34273701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203008 11911636 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203136 22362065 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 203264 86768376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 203264 38822356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203264 20489596 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203392 18332760 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 203520 47946020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203520 24889503 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203648 23056517 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 203776 277371498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 203776 116304918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 203776 55399011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203776 27757139 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 203904 27641872 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 204032 60905907 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204032 27379182 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204160 33526725 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 204288 161066580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 204288 75347027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204288 38057130 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204416 37289897 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 204544 85719553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204544 38228835 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204672 47490718 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 204800 1901878880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 204800 678684993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 204800 269580621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 204800 199289265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 204800 135994339 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 204800 78434747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204800 42198977 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 204928 36235770 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 205056 57559592 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205056 30134151 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205184 27425441 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 205312 63294926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 205312 35454994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205312 23099518 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205440 12355476 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 205568 27839932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205568 10727964 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205696 17111968 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 205824 70291356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 205824 55399616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 205824 32576762 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205824 17563004 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 205952 15013758 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 206080 22822854 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206080 12694935 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206208 10127919 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 206336 14891740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 206336 7358777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206336 5044117 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206464 2314660 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 206592 7532963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206592 5463382 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206720 2069581 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 206848 409104372 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 206848 139953498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 206848 35136063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 206848 11093163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206848 6079765 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 206976 5013398 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 207104 24042900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 207104 8620847 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 207232 15422053 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 207360 104817435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 207360 45830727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 207360 18175390 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 207488 27655337 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 207616 58986708 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 207616 30359393 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 207744 28627315 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 207872 269150874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 207872 121797770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 207872 61160574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 207872 32986356 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208000 28174218 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 208128 60637196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208128 29689053 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208256 30948143 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 208384 147353104 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 208384 66190973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208384 30098751 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208512 36092222 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 208640 81162131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208640 41029448 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208768 40132683 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 208896 1223193887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 208896 687335114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 208896 338724644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 208896 170965250 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 208896 83076990 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 208896 41113360 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209024 41963630 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 209152 87888260 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209152 38959442 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209280 48928818 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 209408 167759394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 209408 89065880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209408 46890004 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209536 42175876 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 209664 78693514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209664 40271712 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209792 38421802 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 209920 348610470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 209920 188241667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 209920 80408725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 209920 38478961 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210048 41929764 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 210176 107832942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210176 51364746 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210304 56468196 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 210432 160368803 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 210432 89873145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210432 48405389 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210560 41467756 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 210688 70495658 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210688 32725943 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210816 37769715 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 210944 535858773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 210944 308932355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 210944 162302786 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 210944 80272225 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 210944 40724145 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211072 39548080 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 211200 82030561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211200 42761846 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211328 39268715 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 211456 146629569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 211456 71007131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211456 34706345 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211584 36300786 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 211712 75622438 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211712 36373443 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211840 39248995 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 211968 226926418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 211968 143674849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 211968 75027513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 211968 37098600 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212096 37928913 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 212224 68647336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212224 36526367 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212352 32120969 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 212480 83251569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 212480 53194025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212480 28935888 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212608 24258137 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 212736 30057544 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212736 15785096 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212864 14272448 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 196608 (MobiusHarmonicTree.branch 2612904564 mobiusHarmonicBlock024 mobiusHarmonicBlock025) = true := Helfgott.combined

#print axioms solution
