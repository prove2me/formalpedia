-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair042_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:29:42.992996+00:00
-- url     : https://prove2.me/submissions/4b67fa7b-ab4a-4814-bb06-43fd3335b512

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688128 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688192 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 30096355 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688256 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688320 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 32753679 d11 d12
private def d6 : MobiusHarmonicTree := .branch 62850034 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688384 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688448 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 33115173 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688512 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688576 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 34635305 d18 d19
private def d13 : MobiusHarmonicTree := .branch 67750478 d14 d17
private def d5 : MobiusHarmonicTree := .branch 130600512 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688640 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688704 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 36021361 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688768 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688832 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 34782171 d26 d27
private def d21 : MobiusHarmonicTree := .branch 70803532 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688896 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688960 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 34600068 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689024 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689088 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 33146806 d33 d34
private def d28 : MobiusHarmonicTree := .branch 67746874 d29 d32
private def d20 : MobiusHarmonicTree := .branch 138550406 d21 d28
private def d4 : MobiusHarmonicTree := .branch 269150918 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689152 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689216 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 35486724 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689280 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689344 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 36579777 d42 d43
private def d37 : MobiusHarmonicTree := .branch 72066501 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689408 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689472 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 35441741 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689536 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689600 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 35729515 d49 d50
private def d44 : MobiusHarmonicTree := .branch 71171256 d45 d48
private def d36 : MobiusHarmonicTree := .branch 143237757 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689664 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689728 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 35638787 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689792 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689856 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 35155262 d57 d58
private def d52 : MobiusHarmonicTree := .branch 70794049 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689920 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 689984 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 35441477 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690048 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690112 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 36146434 d64 d65
private def d59 : MobiusHarmonicTree := .branch 71587911 d60 d63
private def d51 : MobiusHarmonicTree := .branch 142381960 d52 d59
private def d35 : MobiusHarmonicTree := .branch 285619717 d36 d51
private def d3 : MobiusHarmonicTree := .branch 554770635 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690176 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690240 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 37381260 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690304 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690368 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 39014063 d74 d75
private def d69 : MobiusHarmonicTree := .branch 76395323 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690432 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690496 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 37752640 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690560 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690624 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 38400151 d81 d82
private def d76 : MobiusHarmonicTree := .branch 76152791 d77 d80
private def d68 : MobiusHarmonicTree := .branch 152548114 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690688 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690752 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 38149818 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690816 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690880 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 38310649 d89 d90
private def d84 : MobiusHarmonicTree := .branch 76460467 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 690944 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691008 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 40307823 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691072 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691136 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 42276875 d96 d97
private def d91 : MobiusHarmonicTree := .branch 82584698 d92 d95
private def d83 : MobiusHarmonicTree := .branch 159045165 d84 d91
private def d67 : MobiusHarmonicTree := .branch 311593279 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691200 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691264 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 41809008 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691328 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691392 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 40998566 d105 d106
private def d100 : MobiusHarmonicTree := .branch 82807574 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691456 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691520 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 41225219 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691584 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691648 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 42073497 d112 d113
private def d107 : MobiusHarmonicTree := .branch 83298716 d108 d111
private def d99 : MobiusHarmonicTree := .branch 166106290 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691712 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691776 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 40052131 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691840 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691904 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 38303088 d120 d121
private def d115 : MobiusHarmonicTree := .branch 78355219 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 691968 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692032 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 38466535 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692096 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692160 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 38603849 d127 d128
private def d122 : MobiusHarmonicTree := .branch 77070384 d123 d126
private def d114 : MobiusHarmonicTree := .branch 155425603 d115 d122
private def d98 : MobiusHarmonicTree := .branch 321531893 d99 d114
private def d66 : MobiusHarmonicTree := .branch 633125172 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1187895807 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692224 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692288 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 40513580 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692352 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692416 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 39847545 d138 d139
private def d133 : MobiusHarmonicTree := .branch 80361125 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692480 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692544 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 39617798 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692608 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692672 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 41221626 d145 d146
private def d140 : MobiusHarmonicTree := .branch 80839424 d141 d144
private def d132 : MobiusHarmonicTree := .branch 161200549 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692736 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692800 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 40392693 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692864 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692928 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 43819909 d153 d154
private def d148 : MobiusHarmonicTree := .branch 84212602 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 692992 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693056 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 44857942 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693120 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693184 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 46273504 d160 d161
private def d155 : MobiusHarmonicTree := .branch 91131446 d156 d159
private def d147 : MobiusHarmonicTree := .branch 175344048 d148 d155
private def d131 : MobiusHarmonicTree := .branch 336544597 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693248 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693312 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 47952535 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693376 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693440 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 47537028 d169 d170
private def d164 : MobiusHarmonicTree := .branch 95489563 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693504 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693568 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 45375668 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693632 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693696 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 42758075 d176 d177
private def d171 : MobiusHarmonicTree := .branch 88133743 d172 d175
private def d163 : MobiusHarmonicTree := .branch 183623306 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693760 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693824 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 40797208 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693888 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 693952 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 41576409 d184 d185
private def d179 : MobiusHarmonicTree := .branch 82373617 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694016 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694080 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 43617522 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694144 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694208 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 44489672 d191 d192
private def d186 : MobiusHarmonicTree := .branch 88107194 d187 d190
private def d178 : MobiusHarmonicTree := .branch 170480811 d179 d186
private def d162 : MobiusHarmonicTree := .branch 354104117 d163 d178
private def d130 : MobiusHarmonicTree := .branch 690648714 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694272 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694336 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 45349876 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694400 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694464 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 46398463 d201 d202
private def d196 : MobiusHarmonicTree := .branch 91748339 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694528 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694592 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 43609912 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694656 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694720 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 44867061 d208 d209
private def d203 : MobiusHarmonicTree := .branch 88476973 d204 d207
private def d195 : MobiusHarmonicTree := .branch 180225312 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694784 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694848 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 44809897 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694912 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 694976 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 42660598 d216 d217
private def d211 : MobiusHarmonicTree := .branch 87470495 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695040 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695104 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 40953725 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695168 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695232 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 39848699 d223 d224
private def d218 : MobiusHarmonicTree := .branch 80802424 d219 d222
private def d210 : MobiusHarmonicTree := .branch 168272919 d211 d218
private def d194 : MobiusHarmonicTree := .branch 348498231 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695296 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695360 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 36727864 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695424 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695488 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 36499619 d232 d233
private def d227 : MobiusHarmonicTree := .branch 73227483 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695552 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695616 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 37490603 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695680 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695744 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 36650092 d239 d240
private def d234 : MobiusHarmonicTree := .branch 74140695 d235 d238
private def d226 : MobiusHarmonicTree := .branch 147368178 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695808 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695872 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 36692166 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 695936 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696000 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 38504351 d247 d248
private def d242 : MobiusHarmonicTree := .branch 75196517 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696064 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696128 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 40404992 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696192 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock084 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696256 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 39846095 d254 d255
private def d249 : MobiusHarmonicTree := .branch 80251087 d250 d253
private def d241 : MobiusHarmonicTree := .branch 155447604 d242 d249
private def d225 : MobiusHarmonicTree := .branch 302815782 d226 d241
private def d193 : MobiusHarmonicTree := .branch 651314013 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1341962727 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2529858534 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696320 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696384 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 39428034 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696448 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696512 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 40226244 d266 d267
private def d261 : MobiusHarmonicTree := .branch 79654278 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696576 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696640 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 39377732 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696704 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696768 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 39189599 d273 d274
private def d268 : MobiusHarmonicTree := .branch 78567331 d269 d272
private def d260 : MobiusHarmonicTree := .branch 158221609 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696832 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696896 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 40254264 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 696960 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697024 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 40787802 d281 d282
private def d276 : MobiusHarmonicTree := .branch 81042066 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697088 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697152 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 38551263 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697216 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697280 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 39753079 d288 d289
private def d283 : MobiusHarmonicTree := .branch 78304342 d284 d287
private def d275 : MobiusHarmonicTree := .branch 159346408 d276 d283
private def d259 : MobiusHarmonicTree := .branch 317568017 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697344 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697408 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 40122979 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697472 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697536 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 38892701 d297 d298
private def d292 : MobiusHarmonicTree := .branch 79015680 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697600 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697664 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 38663411 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697728 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697792 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 36873525 d304 d305
private def d299 : MobiusHarmonicTree := .branch 75536936 d300 d303
private def d291 : MobiusHarmonicTree := .branch 154552616 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697856 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697920 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 37488686 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 697984 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698048 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 36998960 d312 d313
private def d307 : MobiusHarmonicTree := .branch 74487646 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698112 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698176 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 38993110 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698240 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698304 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 37827479 d319 d320
private def d314 : MobiusHarmonicTree := .branch 76820589 d315 d318
private def d306 : MobiusHarmonicTree := .branch 151308235 d307 d314
private def d290 : MobiusHarmonicTree := .branch 305860851 d291 d306
private def d258 : MobiusHarmonicTree := .branch 623428868 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698368 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698432 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 36937133 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698496 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698560 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 35556090 d329 d330
private def d324 : MobiusHarmonicTree := .branch 72493223 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698624 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698688 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 36322444 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698752 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698816 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 39226375 d336 d337
private def d331 : MobiusHarmonicTree := .branch 75548819 d332 d335
private def d323 : MobiusHarmonicTree := .branch 148042042 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698880 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 698944 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 42429784 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699008 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699072 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 41824160 d344 d345
private def d339 : MobiusHarmonicTree := .branch 84253944 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699136 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699200 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 39189197 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699264 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699328 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 38099516 d351 d352
private def d346 : MobiusHarmonicTree := .branch 77288713 d347 d350
private def d338 : MobiusHarmonicTree := .branch 161542657 d339 d346
private def d322 : MobiusHarmonicTree := .branch 309584699 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699392 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699456 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 38744455 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699520 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699584 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 38441503 d360 d361
private def d355 : MobiusHarmonicTree := .branch 77185958 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699648 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699712 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 39081866 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699776 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699840 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 39701984 d367 d368
private def d362 : MobiusHarmonicTree := .branch 78783850 d363 d366
private def d354 : MobiusHarmonicTree := .branch 155969808 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699904 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 699968 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 41644868 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700032 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700096 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 40923089 d375 d376
private def d370 : MobiusHarmonicTree := .branch 82567957 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700160 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700224 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 39180464 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700288 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700352 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 38212320 d382 d383
private def d377 : MobiusHarmonicTree := .branch 77392784 d378 d381
private def d369 : MobiusHarmonicTree := .branch 159960741 d370 d377
private def d353 : MobiusHarmonicTree := .branch 315930549 d354 d369
private def d321 : MobiusHarmonicTree := .branch 625515248 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1248944116 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700416 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700480 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 37103224 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700544 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700608 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 36495566 d393 d394
private def d388 : MobiusHarmonicTree := .branch 73598790 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700672 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700736 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 35126018 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700800 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700864 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 36382290 d400 d401
private def d395 : MobiusHarmonicTree := .branch 71508308 d396 d399
private def d387 : MobiusHarmonicTree := .branch 145107098 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700928 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 700992 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 37459848 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701056 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701120 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 39926180 d408 d409
private def d403 : MobiusHarmonicTree := .branch 77386028 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701184 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701248 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 41036930 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701312 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701376 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 41612588 d415 d416
private def d410 : MobiusHarmonicTree := .branch 82649518 d411 d414
private def d402 : MobiusHarmonicTree := .branch 160035546 d403 d410
private def d386 : MobiusHarmonicTree := .branch 305142644 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701440 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701504 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 39798877 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701568 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701632 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 38320803 d424 d425
private def d419 : MobiusHarmonicTree := .branch 78119680 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701696 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701760 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 37789363 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701824 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701888 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 37828056 d431 d432
private def d426 : MobiusHarmonicTree := .branch 75617419 d427 d430
private def d418 : MobiusHarmonicTree := .branch 153737099 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 701952 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702016 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 39427934 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702080 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702144 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 41424655 d439 d440
private def d434 : MobiusHarmonicTree := .branch 80852589 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702208 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702272 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 40359129 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702336 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702400 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 35746170 d446 d447
private def d441 : MobiusHarmonicTree := .branch 76105299 d442 d445
private def d433 : MobiusHarmonicTree := .branch 156957888 d434 d441
private def d417 : MobiusHarmonicTree := .branch 310694987 d418 d433
private def d385 : MobiusHarmonicTree := .branch 615837631 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702464 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702528 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 34827154 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702592 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702656 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 36878687 d456 d457
private def d451 : MobiusHarmonicTree := .branch 71705841 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702720 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702784 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 38010354 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702848 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702912 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 38778739 d463 d464
private def d458 : MobiusHarmonicTree := .branch 76789093 d459 d462
private def d450 : MobiusHarmonicTree := .branch 148494934 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 702976 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703040 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 39918152 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703104 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703168 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 38717751 d471 d472
private def d466 : MobiusHarmonicTree := .branch 78635903 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703232 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703296 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 36646104 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703360 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703424 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 38895503 d478 d479
private def d473 : MobiusHarmonicTree := .branch 75541607 d474 d477
private def d465 : MobiusHarmonicTree := .branch 154177510 d466 d473
private def d449 : MobiusHarmonicTree := .branch 302672444 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703488 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703552 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 39394471 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703616 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703680 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 41320006 d487 d488
private def d482 : MobiusHarmonicTree := .branch 80714477 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703744 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703808 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 40542428 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703872 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 703936 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 40209726 d494 d495
private def d489 : MobiusHarmonicTree := .branch 80752154 d490 d493
private def d481 : MobiusHarmonicTree := .branch 161466631 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704000 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704064 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 37838988 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704128 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704192 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 38421425 d502 d503
private def d497 : MobiusHarmonicTree := .branch 76260413 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704256 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704320 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 36514790 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704384 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock085 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704448 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 34640001 d509 d510
private def d504 : MobiusHarmonicTree := .branch 71154791 d505 d508
private def d496 : MobiusHarmonicTree := .branch 147415204 d497 d504
private def d480 : MobiusHarmonicTree := .branch 308881835 d481 d496
private def d448 : MobiusHarmonicTree := .branch 611554279 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1227391910 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2476336026 d257 d384
private def d0 : MobiusHarmonicTree := .branch 5006194560 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 688128 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 688128 5006194560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 688128 2529858534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 688128 1187895807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 688128 554770635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 688128 269150918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 688128 130600512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 688128 62850034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688128 30096355 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688256 32753679 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 688384 67750478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688384 33115173 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688512 34635305 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 688640 138550406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 688640 70803532 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688640 36021361 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688768 34782171 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 688896 67746874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688896 34600068 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689024 33146806 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 689152 285619717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 689152 143237757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 689152 72066501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689152 35486724 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689280 36579777 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 689408 71171256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689408 35441741 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689536 35729515 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 689664 142381960 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 689664 70794049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689664 35638787 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689792 35155262 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 689920 71587911 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 689920 35441477 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690048 36146434 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 690176 633125172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 690176 311593279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 690176 152548114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 690176 76395323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690176 37381260 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690304 39014063 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 690432 76152791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690432 37752640 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690560 38400151 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 690688 159045165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 690688 76460467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690688 38149818 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690816 38310649 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 690944 82584698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 690944 40307823 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691072 42276875 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 691200 321531893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 691200 166106290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 691200 82807574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691200 41809008 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691328 40998566 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 691456 83298716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691456 41225219 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691584 42073497 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 691712 155425603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 691712 78355219 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691712 40052131 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691840 38303088 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 691968 77070384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 691968 38466535 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692096 38603849 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 692224 1341962727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 692224 690648714 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 692224 336544597 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 692224 161200549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 692224 80361125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692224 40513580 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692352 39847545 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 692480 80839424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692480 39617798 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692608 41221626 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 692736 175344048 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 692736 84212602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692736 40392693 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692864 43819909 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 692992 91131446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 692992 44857942 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 693120 46273504 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 693248 354104117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 693248 183623306 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 693248 95489563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 693248 47952535 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 693376 47537028 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 693504 88133743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 693504 45375668 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 693632 42758075 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 693760 170480811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 693760 82373617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 693760 40797208 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 693888 41576409 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 694016 88107194 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694016 43617522 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694144 44489672 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 694272 651314013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 694272 348498231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 694272 180225312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 694272 91748339 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694272 45349876 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694400 46398463 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 694528 88476973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694528 43609912 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694656 44867061 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 694784 168272919 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 694784 87470495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694784 44809897 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 694912 42660598 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 695040 80802424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695040 40953725 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695168 39848699 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 695296 302815782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 695296 147368178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 695296 73227483 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695296 36727864 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695424 36499619 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 695552 74140695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695552 37490603 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695680 36650092 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 695808 155447604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 695808 75196517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695808 36692166 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 695936 38504351 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 696064 80251087 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696064 40404992 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696192 39846095 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 696320 2476336026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 696320 1248944116 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 696320 623428868 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 696320 317568017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 696320 158221609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 696320 79654278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696320 39428034 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696448 40226244 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 696576 78567331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696576 39377732 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696704 39189599 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 696832 159346408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 696832 81042066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696832 40254264 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 696960 40787802 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 697088 78304342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697088 38551263 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697216 39753079 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 697344 305860851 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 697344 154552616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 697344 79015680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697344 40122979 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697472 38892701 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 697600 75536936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697600 38663411 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697728 36873525 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 697856 151308235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 697856 74487646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697856 37488686 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 697984 36998960 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 698112 76820589 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 698112 38993110 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 698240 37827479 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 698368 625515248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 698368 309584699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 698368 148042042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 698368 72493223 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 698368 36937133 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 698496 35556090 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 698624 75548819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 698624 36322444 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 698752 39226375 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 698880 161542657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 698880 84253944 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 698880 42429784 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699008 41824160 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 699136 77288713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699136 39189197 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699264 38099516 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 699392 315930549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 699392 155969808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 699392 77185958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699392 38744455 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699520 38441503 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 699648 78783850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699648 39081866 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699776 39701984 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 699904 159960741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 699904 82567957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 699904 41644868 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700032 40923089 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 700160 77392784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700160 39180464 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700288 38212320 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 700416 1227391910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 700416 615837631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 700416 305142644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 700416 145107098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 700416 73598790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700416 37103224 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700544 36495566 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 700672 71508308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700672 35126018 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700800 36382290 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 700928 160035546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 700928 77386028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 700928 37459848 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701056 39926180 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 701184 82649518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701184 41036930 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701312 41612588 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 701440 310694987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 701440 153737099 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 701440 78119680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701440 39798877 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701568 38320803 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 701696 75617419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701696 37789363 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701824 37828056 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 701952 156957888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 701952 80852589 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 701952 39427934 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702080 41424655 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 702208 76105299 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702208 40359129 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702336 35746170 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 702464 611554279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 702464 302672444 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 702464 148494934 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 702464 71705841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702464 34827154 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702592 36878687 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 702720 76789093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702720 38010354 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702848 38778739 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 702976 154177510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 702976 78635903 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 702976 39918152 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 703104 38717751 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 703232 75541607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 703232 36646104 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 703360 38895503 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 703488 308881835 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 703488 161466631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 703488 80714477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 703488 39394471 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 703616 41320006 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 703744 80752154 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 703744 40542428 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 703872 40209726 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 704000 147415204 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 704000 76260413 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704000 37838988 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704128 38421425 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 704256 71154791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704256 36514790 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704384 34640001 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 688128 (MobiusHarmonicTree.branch 5006194560 mobiusHarmonicBlock084 mobiusHarmonicBlock085) = true := Helfgott.combined

#print axioms solution
