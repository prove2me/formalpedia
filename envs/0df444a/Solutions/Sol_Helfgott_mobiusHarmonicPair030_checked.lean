-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair030_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:46:53.987227+00:00
-- url     : https://prove2.me/submissions/345d8d44-6180-4e34-96d5-0c05f61c4fdf

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491520 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491584 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 3751200 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491648 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491712 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 2094892 d11 d12
private def d6 : MobiusHarmonicTree := .branch 5846092 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491776 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491840 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 1347994 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491904 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491968 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 2628338 d18 d19
private def d13 : MobiusHarmonicTree := .branch 3976332 d14 d17
private def d5 : MobiusHarmonicTree := .branch 9822424 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492032 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492096 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 3661910 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492160 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492224 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 2381127 d26 d27
private def d21 : MobiusHarmonicTree := .branch 6043037 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492288 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492352 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 743454 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492416 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492480 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 946262 d33 d34
private def d28 : MobiusHarmonicTree := .branch 1689716 d29 d32
private def d20 : MobiusHarmonicTree := .branch 7732753 d21 d28
private def d4 : MobiusHarmonicTree := .branch 17555177 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492544 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492608 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 2224996 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492672 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492736 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 2496306 d42 d43
private def d37 : MobiusHarmonicTree := .branch 4721302 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492800 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492864 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 1400099 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492928 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 492992 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 1288112 d49 d50
private def d44 : MobiusHarmonicTree := .branch 2688211 d45 d48
private def d36 : MobiusHarmonicTree := .branch 7409513 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493056 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493120 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 594223 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493184 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493248 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 2088291 d57 d58
private def d52 : MobiusHarmonicTree := .branch 2682514 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493312 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493376 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 865543 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493440 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493504 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 2151934 d64 d65
private def d59 : MobiusHarmonicTree := .branch 3017477 d60 d63
private def d51 : MobiusHarmonicTree := .branch 5699991 d52 d59
private def d35 : MobiusHarmonicTree := .branch 13109504 d36 d51
private def d3 : MobiusHarmonicTree := .branch 30664681 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493568 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493632 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 4543969 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493696 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493760 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 1986906 d74 d75
private def d69 : MobiusHarmonicTree := .branch 6530875 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493824 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493888 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 3002723 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 493952 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494016 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 3271186 d81 d82
private def d76 : MobiusHarmonicTree := .branch 6273909 d77 d80
private def d68 : MobiusHarmonicTree := .branch 12804784 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494080 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494144 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 3063987 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494208 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494272 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 1578200 d89 d90
private def d84 : MobiusHarmonicTree := .branch 4642187 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494336 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494400 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 1391575 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494464 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494528 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 1207297 d96 d97
private def d91 : MobiusHarmonicTree := .branch 2598872 d92 d95
private def d83 : MobiusHarmonicTree := .branch 7241059 d84 d91
private def d67 : MobiusHarmonicTree := .branch 20045843 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494592 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494656 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 2640280 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494720 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494784 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 3876479 d105 d106
private def d100 : MobiusHarmonicTree := .branch 6516759 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494848 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494912 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 3978486 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 494976 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495040 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 6025798 d112 d113
private def d107 : MobiusHarmonicTree := .branch 10004284 d108 d111
private def d99 : MobiusHarmonicTree := .branch 16521043 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495104 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495168 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 5779936 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495232 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495296 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 6083222 d120 d121
private def d115 : MobiusHarmonicTree := .branch 11863158 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495360 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495424 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 10825045 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495488 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495552 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 14385989 d127 d128
private def d122 : MobiusHarmonicTree := .branch 25211034 d123 d126
private def d114 : MobiusHarmonicTree := .branch 37074192 d115 d122
private def d98 : MobiusHarmonicTree := .branch 53595235 d99 d114
private def d66 : MobiusHarmonicTree := .branch 73641078 d67 d98
private def d2 : MobiusHarmonicTree := .branch 104305759 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495616 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495680 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 16545026 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495744 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495808 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 16591167 d138 d139
private def d133 : MobiusHarmonicTree := .branch 33136193 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495872 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 495936 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 15465789 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496000 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496064 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 13460055 d145 d146
private def d140 : MobiusHarmonicTree := .branch 28925844 d141 d144
private def d132 : MobiusHarmonicTree := .branch 62062037 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496128 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496192 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 10608921 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496256 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496320 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 11456372 d153 d154
private def d148 : MobiusHarmonicTree := .branch 22065293 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496384 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496448 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 10661819 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496512 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496576 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 8597040 d160 d161
private def d155 : MobiusHarmonicTree := .branch 19258859 d156 d159
private def d147 : MobiusHarmonicTree := .branch 41324152 d148 d155
private def d131 : MobiusHarmonicTree := .branch 103386189 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496640 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496704 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 5405733 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496768 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496832 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 2995126 d169 d170
private def d164 : MobiusHarmonicTree := .branch 8400859 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496896 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 496960 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 1970126 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497024 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497088 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 573392 d176 d177
private def d171 : MobiusHarmonicTree := .branch 2543518 d172 d175
private def d163 : MobiusHarmonicTree := .branch 10944377 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497152 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497216 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 1176638 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497280 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497344 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 2615851 d184 d185
private def d179 : MobiusHarmonicTree := .branch 3792489 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497408 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497472 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6334061 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497536 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497600 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 6692220 d191 d192
private def d186 : MobiusHarmonicTree := .branch 13026281 d187 d190
private def d178 : MobiusHarmonicTree := .branch 16818770 d179 d186
private def d162 : MobiusHarmonicTree := .branch 27763147 d163 d178
private def d130 : MobiusHarmonicTree := .branch 131149336 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497664 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497728 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 5955114 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497792 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497856 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 4585743 d201 d202
private def d196 : MobiusHarmonicTree := .branch 10540857 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497920 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 497984 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 3556354 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498048 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498112 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 3910874 d208 d209
private def d203 : MobiusHarmonicTree := .branch 7467228 d204 d207
private def d195 : MobiusHarmonicTree := .branch 18008085 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498176 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498240 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 2543061 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498304 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498368 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 1629340 d216 d217
private def d211 : MobiusHarmonicTree := .branch 4172401 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498432 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498496 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 2991061 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498560 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498624 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 3269099 d223 d224
private def d218 : MobiusHarmonicTree := .branch 6260160 d219 d222
private def d210 : MobiusHarmonicTree := .branch 10432561 d211 d218
private def d194 : MobiusHarmonicTree := .branch 28440646 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498688 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498752 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 3143901 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498816 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498880 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 2120903 d232 d233
private def d227 : MobiusHarmonicTree := .branch 5264804 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 498944 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499008 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 773584 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499072 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499136 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 1863298 d239 d240
private def d234 : MobiusHarmonicTree := .branch 2636882 d235 d238
private def d226 : MobiusHarmonicTree := .branch 7901686 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499200 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499264 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 2173331 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499328 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499392 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 2192687 d247 d248
private def d242 : MobiusHarmonicTree := .branch 4366018 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499456 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499520 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 3571459 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499584 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock060 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499648 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 4931499 d254 d255
private def d249 : MobiusHarmonicTree := .branch 8502958 d250 d253
private def d241 : MobiusHarmonicTree := .branch 12868976 d242 d249
private def d225 : MobiusHarmonicTree := .branch 20770662 d226 d241
private def d193 : MobiusHarmonicTree := .branch 49211308 d194 d225
private def d129 : MobiusHarmonicTree := .branch 180360644 d130 d193
private def d1 : MobiusHarmonicTree := .branch 284666403 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499712 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499776 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 5244404 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499840 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499904 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 3846778 d266 d267
private def d261 : MobiusHarmonicTree := .branch 9091182 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 499968 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500032 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 1837978 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500096 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500160 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 1909397 d273 d274
private def d268 : MobiusHarmonicTree := .branch 3747375 d269 d272
private def d260 : MobiusHarmonicTree := .branch 12838557 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500224 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500288 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 4637380 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500352 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500416 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 4788058 d281 d282
private def d276 : MobiusHarmonicTree := .branch 9425438 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500480 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500544 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 7461950 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500608 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500672 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 9193629 d288 d289
private def d283 : MobiusHarmonicTree := .branch 16655579 d284 d287
private def d275 : MobiusHarmonicTree := .branch 26081017 d276 d283
private def d259 : MobiusHarmonicTree := .branch 38919574 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500736 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500800 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 11148195 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500864 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500928 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 13586805 d297 d298
private def d292 : MobiusHarmonicTree := .branch 24735000 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 500992 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501056 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 15964401 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501120 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501184 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 15842532 d304 d305
private def d299 : MobiusHarmonicTree := .branch 31806933 d300 d303
private def d291 : MobiusHarmonicTree := .branch 56541933 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501248 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501312 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 17430299 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501376 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501440 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 17583468 d312 d313
private def d307 : MobiusHarmonicTree := .branch 35013767 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501504 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501568 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 17365606 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501632 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501696 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 17941252 d319 d320
private def d314 : MobiusHarmonicTree := .branch 35306858 d315 d318
private def d306 : MobiusHarmonicTree := .branch 70320625 d307 d314
private def d290 : MobiusHarmonicTree := .branch 126862558 d291 d306
private def d258 : MobiusHarmonicTree := .branch 165782132 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501760 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501824 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 18608137 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501888 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 501952 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 16324403 d329 d330
private def d324 : MobiusHarmonicTree := .branch 34932540 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502016 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502080 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 16176712 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502144 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502208 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 17996623 d336 d337
private def d331 : MobiusHarmonicTree := .branch 34173335 d332 d335
private def d323 : MobiusHarmonicTree := .branch 69105875 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502272 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502336 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 13519096 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502400 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502464 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 8390788 d344 d345
private def d339 : MobiusHarmonicTree := .branch 21909884 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502528 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502592 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 6416838 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502656 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502720 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 6844849 d351 d352
private def d346 : MobiusHarmonicTree := .branch 13261687 d347 d350
private def d338 : MobiusHarmonicTree := .branch 35171571 d339 d346
private def d322 : MobiusHarmonicTree := .branch 104277446 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502784 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502848 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 6276332 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502912 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 502976 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 4067913 d360 d361
private def d355 : MobiusHarmonicTree := .branch 10344245 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503040 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503104 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 976028 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503168 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503232 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 961855 d367 d368
private def d362 : MobiusHarmonicTree := .branch 1937883 d363 d366
private def d354 : MobiusHarmonicTree := .branch 12282128 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503296 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503360 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 609950 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503424 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503488 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 1618727 d375 d376
private def d370 : MobiusHarmonicTree := .branch 2228677 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503552 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503616 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 2803783 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503680 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503744 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 2622432 d382 d383
private def d377 : MobiusHarmonicTree := .branch 5426215 d378 d381
private def d369 : MobiusHarmonicTree := .branch 7654892 d370 d377
private def d353 : MobiusHarmonicTree := .branch 19937020 d354 d369
private def d321 : MobiusHarmonicTree := .branch 124214466 d322 d353
private def d257 : MobiusHarmonicTree := .branch 289996598 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503808 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503872 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 5828857 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 503936 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504000 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 8331374 d393 d394
private def d388 : MobiusHarmonicTree := .branch 14160231 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504064 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504128 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 10721470 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504192 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504256 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 11476439 d400 d401
private def d395 : MobiusHarmonicTree := .branch 22197909 d396 d399
private def d387 : MobiusHarmonicTree := .branch 36358140 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504320 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504384 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 12056299 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504448 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504512 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 12382318 d408 d409
private def d403 : MobiusHarmonicTree := .branch 24438617 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504576 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504640 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 12404963 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504704 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504768 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 12990185 d415 d416
private def d410 : MobiusHarmonicTree := .branch 25395148 d411 d414
private def d402 : MobiusHarmonicTree := .branch 49833765 d403 d410
private def d386 : MobiusHarmonicTree := .branch 86191905 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504832 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504896 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 12267989 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 504960 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505024 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 13456813 d424 d425
private def d419 : MobiusHarmonicTree := .branch 25724802 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505088 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505152 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 16472285 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505216 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505280 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 18920204 d431 d432
private def d426 : MobiusHarmonicTree := .branch 35392489 d427 d430
private def d418 : MobiusHarmonicTree := .branch 61117291 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505344 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505408 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 21137471 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505472 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505536 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 20831471 d439 d440
private def d434 : MobiusHarmonicTree := .branch 41968942 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505600 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505664 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 19965870 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505728 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505792 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 20162564 d446 d447
private def d441 : MobiusHarmonicTree := .branch 40128434 d442 d445
private def d433 : MobiusHarmonicTree := .branch 82097376 d434 d441
private def d417 : MobiusHarmonicTree := .branch 143214667 d418 d433
private def d385 : MobiusHarmonicTree := .branch 229406572 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505856 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505920 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 18692761 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 505984 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506048 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 17781036 d456 d457
private def d451 : MobiusHarmonicTree := .branch 36473797 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506112 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506176 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 19854772 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506240 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506304 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 23367420 d463 d464
private def d458 : MobiusHarmonicTree := .branch 43222192 d459 d462
private def d450 : MobiusHarmonicTree := .branch 79695989 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506368 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506432 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 25713248 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506496 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506560 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 29763535 d471 d472
private def d466 : MobiusHarmonicTree := .branch 55476783 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506624 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506688 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 29041721 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506752 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506816 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 29381533 d478 d479
private def d473 : MobiusHarmonicTree := .branch 58423254 d474 d477
private def d465 : MobiusHarmonicTree := .branch 113900037 d466 d473
private def d449 : MobiusHarmonicTree := .branch 193596026 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506880 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 506944 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 29892969 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507008 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507072 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 29246404 d487 d488
private def d482 : MobiusHarmonicTree := .branch 59139373 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507136 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507200 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 31445341 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507264 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507328 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 27926832 d494 d495
private def d489 : MobiusHarmonicTree := .branch 59372173 d490 d493
private def d481 : MobiusHarmonicTree := .branch 118511546 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507392 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507456 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 27551338 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507520 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507584 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 23844448 d502 d503
private def d497 : MobiusHarmonicTree := .branch 51395786 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507648 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507712 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 20535431 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507776 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock061 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507840 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 19484611 d509 d510
private def d504 : MobiusHarmonicTree := .branch 40020042 d505 d508
private def d496 : MobiusHarmonicTree := .branch 91415828 d497 d504
private def d480 : MobiusHarmonicTree := .branch 209927374 d481 d496
private def d448 : MobiusHarmonicTree := .branch 403523400 d449 d480
private def d384 : MobiusHarmonicTree := .branch 632929972 d385 d448
private def d256 : MobiusHarmonicTree := .branch 922926570 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1207592973 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 491520 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 491520 1207592973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 491520 284666403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 491520 104305759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 491520 30664681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 491520 17555177 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 491520 9822424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 491520 5846092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491520 3751200 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491648 2094892 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 491776 3976332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491776 1347994 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491904 2628338 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 492032 7732753 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 492032 6043037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492032 3661910 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492160 2381127 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 492288 1689716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492288 743454 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492416 946262 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 492544 13109504 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 492544 7409513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 492544 4721302 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492544 2224996 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492672 2496306 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 492800 2688211 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492800 1400099 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 492928 1288112 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 493056 5699991 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 493056 2682514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493056 594223 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493184 2088291 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 493312 3017477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493312 865543 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493440 2151934 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 493568 73641078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 493568 20045843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 493568 12804784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 493568 6530875 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493568 4543969 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493696 1986906 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 493824 6273909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493824 3002723 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 493952 3271186 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 494080 7241059 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 494080 4642187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494080 3063987 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494208 1578200 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 494336 2598872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494336 1391575 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494464 1207297 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 494592 53595235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 494592 16521043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 494592 6516759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494592 2640280 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494720 3876479 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 494848 10004284 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494848 3978486 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 494976 6025798 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 495104 37074192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 495104 11863158 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 495104 5779936 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 495232 6083222 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 495360 25211034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 495360 10825045 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 495488 14385989 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 495616 180360644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 495616 131149336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 495616 103386189 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 495616 62062037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 495616 33136193 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 495616 16545026 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 495744 16591167 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 495872 28925844 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 495872 15465789 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496000 13460055 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 496128 41324152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 496128 22065293 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496128 10608921 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496256 11456372 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 496384 19258859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496384 10661819 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496512 8597040 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 496640 27763147 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 496640 10944377 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 496640 8400859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496640 5405733 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496768 2995126 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 496896 2543518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 496896 1970126 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497024 573392 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 497152 16818770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 497152 3792489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497152 1176638 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497280 2615851 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 497408 13026281 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497408 6334061 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497536 6692220 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 497664 49211308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 497664 28440646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 497664 18008085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 497664 10540857 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497664 5955114 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497792 4585743 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 497920 7467228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 497920 3556354 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498048 3910874 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 498176 10432561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 498176 4172401 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498176 2543061 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498304 1629340 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 498432 6260160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498432 2991061 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498560 3269099 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 498688 20770662 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 498688 7901686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 498688 5264804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498688 3143901 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498816 2120903 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 498944 2636882 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 498944 773584 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499072 1863298 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 499200 12868976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 499200 4366018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499200 2173331 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499328 2192687 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 499456 8502958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499456 3571459 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499584 4931499 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 499712 922926570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 499712 289996598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 499712 165782132 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 499712 38919574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 499712 12838557 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 499712 9091182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499712 5244404 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499840 3846778 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 499968 3747375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 499968 1837978 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500096 1909397 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 500224 26081017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 500224 9425438 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500224 4637380 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500352 4788058 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 500480 16655579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500480 7461950 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500608 9193629 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 500736 126862558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 500736 56541933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 500736 24735000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500736 11148195 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500864 13586805 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 500992 31806933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 500992 15964401 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 501120 15842532 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 501248 70320625 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 501248 35013767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 501248 17430299 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 501376 17583468 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 501504 35306858 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 501504 17365606 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 501632 17941252 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 501760 124214466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 501760 104277446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 501760 69105875 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 501760 34932540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 501760 18608137 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 501888 16324403 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 502016 34173335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502016 16176712 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502144 17996623 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 502272 35171571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 502272 21909884 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502272 13519096 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502400 8390788 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 502528 13261687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502528 6416838 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502656 6844849 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 502784 19937020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 502784 12282128 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 502784 10344245 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502784 6276332 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 502912 4067913 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 503040 1937883 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503040 976028 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503168 961855 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 503296 7654892 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 503296 2228677 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503296 609950 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503424 1618727 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 503552 5426215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503552 2803783 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503680 2622432 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 503808 632929972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 503808 229406572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 503808 86191905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 503808 36358140 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 503808 14160231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503808 5828857 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 503936 8331374 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 504064 22197909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504064 10721470 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504192 11476439 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 504320 49833765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 504320 24438617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504320 12056299 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504448 12382318 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 504576 25395148 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504576 12404963 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504704 12990185 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 504832 143214667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 504832 61117291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 504832 25724802 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504832 12267989 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 504960 13456813 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 505088 35392489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505088 16472285 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505216 18920204 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 505344 82097376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 505344 41968942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505344 21137471 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505472 20831471 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 505600 40128434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505600 19965870 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505728 20162564 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 505856 403523400 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 505856 193596026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 505856 79695989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 505856 36473797 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505856 18692761 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 505984 17781036 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 506112 43222192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 506112 19854772 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 506240 23367420 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 506368 113900037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 506368 55476783 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 506368 25713248 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 506496 29763535 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 506624 58423254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 506624 29041721 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 506752 29381533 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 506880 209927374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 506880 118511546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 506880 59139373 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 506880 29892969 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507008 29246404 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 507136 59372173 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507136 31445341 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507264 27926832 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 507392 91415828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 507392 51395786 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507392 27551338 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507520 23844448 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 507648 40020042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507648 20535431 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507776 19484611 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 491520 (MobiusHarmonicTree.branch 1207592973 mobiusHarmonicBlock060 mobiusHarmonicBlock061) = true := Helfgott.combined

#print axioms solution
