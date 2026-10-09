-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair045_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:41:55.366579+00:00
-- url     : https://prove2.me/submissions/9c2e7998-9301-4058-8981-004a2e56da79

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737280 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737344 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 13857951 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737408 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737472 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 13242599 d11 d12
private def d6 : MobiusHarmonicTree := .branch 27100550 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737536 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737600 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 12411987 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737664 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737728 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 10600187 d18 d19
private def d13 : MobiusHarmonicTree := .branch 23012174 d14 d17
private def d5 : MobiusHarmonicTree := .branch 50112724 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737792 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737856 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 11282773 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737920 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737984 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 11150739 d26 d27
private def d21 : MobiusHarmonicTree := .branch 22433512 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738048 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738112 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 10674614 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738176 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738240 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 9769258 d33 d34
private def d28 : MobiusHarmonicTree := .branch 20443872 d29 d32
private def d20 : MobiusHarmonicTree := .branch 42877384 d21 d28
private def d4 : MobiusHarmonicTree := .branch 92990108 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738304 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738368 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 10353981 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738432 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738496 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 9537035 d42 d43
private def d37 : MobiusHarmonicTree := .branch 19891016 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738560 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738624 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 10335484 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738688 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738752 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 11209516 d49 d50
private def d44 : MobiusHarmonicTree := .branch 21545000 d45 d48
private def d36 : MobiusHarmonicTree := .branch 41436016 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738816 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738880 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 10493018 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 738944 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739008 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 9193493 d57 d58
private def d52 : MobiusHarmonicTree := .branch 19686511 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739072 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739136 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 8189363 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739200 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739264 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 6682433 d64 d65
private def d59 : MobiusHarmonicTree := .branch 14871796 d60 d63
private def d51 : MobiusHarmonicTree := .branch 34558307 d52 d59
private def d35 : MobiusHarmonicTree := .branch 75994323 d36 d51
private def d3 : MobiusHarmonicTree := .branch 168984431 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739328 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739392 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 4801343 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739456 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739520 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 2722114 d74 d75
private def d69 : MobiusHarmonicTree := .branch 7523457 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739584 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739648 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 2996110 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739712 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739776 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 2811707 d81 d82
private def d76 : MobiusHarmonicTree := .branch 5807817 d77 d80
private def d68 : MobiusHarmonicTree := .branch 13331274 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739840 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739904 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 4065422 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 739968 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740032 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 5201190 d89 d90
private def d84 : MobiusHarmonicTree := .branch 9266612 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740096 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740160 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 5881229 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740224 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740288 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 6935180 d96 d97
private def d91 : MobiusHarmonicTree := .branch 12816409 d92 d95
private def d83 : MobiusHarmonicTree := .branch 22083021 d84 d91
private def d67 : MobiusHarmonicTree := .branch 35414295 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740352 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740416 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 8847779 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740480 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740544 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 9576844 d105 d106
private def d100 : MobiusHarmonicTree := .branch 18424623 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740608 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740672 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 5593687 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740736 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740800 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 7251621 d112 d113
private def d107 : MobiusHarmonicTree := .branch 12845308 d108 d111
private def d99 : MobiusHarmonicTree := .branch 31269931 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740864 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740928 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 8415215 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 740992 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741056 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 7922526 d120 d121
private def d115 : MobiusHarmonicTree := .branch 16337741 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741120 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741184 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 8288160 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741248 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741312 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 7587984 d127 d128
private def d122 : MobiusHarmonicTree := .branch 15876144 d123 d126
private def d114 : MobiusHarmonicTree := .branch 32213885 d115 d122
private def d98 : MobiusHarmonicTree := .branch 63483816 d99 d114
private def d66 : MobiusHarmonicTree := .branch 98898111 d67 d98
private def d2 : MobiusHarmonicTree := .branch 267882542 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741376 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741440 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 6728911 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741504 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741568 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 4366506 d138 d139
private def d133 : MobiusHarmonicTree := .branch 11095417 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741632 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741696 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 2083151 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741760 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741824 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 2999453 d145 d146
private def d140 : MobiusHarmonicTree := .branch 5082604 d141 d144
private def d132 : MobiusHarmonicTree := .branch 16178021 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741888 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 741952 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 1842522 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742016 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742080 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 2187133 d153 d154
private def d148 : MobiusHarmonicTree := .branch 4029655 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742144 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742208 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 2301346 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742272 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742336 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 1333691 d160 d161
private def d155 : MobiusHarmonicTree := .branch 3635037 d156 d159
private def d147 : MobiusHarmonicTree := .branch 7664692 d148 d155
private def d131 : MobiusHarmonicTree := .branch 23842713 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742400 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742464 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 1530085 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742528 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742592 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 2029431 d169 d170
private def d164 : MobiusHarmonicTree := .branch 3559516 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742656 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742720 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 2286268 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742784 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742848 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 4411423 d176 d177
private def d171 : MobiusHarmonicTree := .branch 6697691 d172 d175
private def d163 : MobiusHarmonicTree := .branch 10257207 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742912 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 742976 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 4640883 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743040 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743104 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 3362996 d184 d185
private def d179 : MobiusHarmonicTree := .branch 8003879 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743168 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743232 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 2462304 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743296 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743360 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 1891485 d191 d192
private def d186 : MobiusHarmonicTree := .branch 4353789 d187 d190
private def d178 : MobiusHarmonicTree := .branch 12357668 d179 d186
private def d162 : MobiusHarmonicTree := .branch 22614875 d163 d178
private def d130 : MobiusHarmonicTree := .branch 46457588 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743424 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743488 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 2411667 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743552 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743616 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 2711151 d201 d202
private def d196 : MobiusHarmonicTree := .branch 5122818 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743680 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743744 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 3735213 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743808 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743872 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 3332617 d208 d209
private def d203 : MobiusHarmonicTree := .branch 7067830 d204 d207
private def d195 : MobiusHarmonicTree := .branch 12190648 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 743936 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744000 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 5040347 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744064 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744128 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 7314650 d216 d217
private def d211 : MobiusHarmonicTree := .branch 12354997 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744192 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744256 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 8321087 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744320 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744384 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 9535514 d223 d224
private def d218 : MobiusHarmonicTree := .branch 17856601 d219 d222
private def d210 : MobiusHarmonicTree := .branch 30211598 d211 d218
private def d194 : MobiusHarmonicTree := .branch 42402246 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744448 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744512 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 10503545 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744576 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744640 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 14159895 d232 d233
private def d227 : MobiusHarmonicTree := .branch 24663440 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744704 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744768 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 13812422 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744832 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744896 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 14606138 d239 d240
private def d234 : MobiusHarmonicTree := .branch 28418560 d235 d238
private def d226 : MobiusHarmonicTree := .branch 53082000 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 744960 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745024 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 14180856 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745088 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745152 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 12722328 d247 d248
private def d242 : MobiusHarmonicTree := .branch 26903184 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745216 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745280 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 13063566 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745344 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock090 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745408 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 15752491 d254 d255
private def d249 : MobiusHarmonicTree := .branch 28816057 d250 d253
private def d241 : MobiusHarmonicTree := .branch 55719241 d242 d249
private def d225 : MobiusHarmonicTree := .branch 108801241 d226 d241
private def d193 : MobiusHarmonicTree := .branch 151203487 d194 d225
private def d129 : MobiusHarmonicTree := .branch 197661075 d130 d193
private def d1 : MobiusHarmonicTree := .branch 465543617 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745472 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745536 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 18233892 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745600 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745664 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 18845037 d266 d267
private def d261 : MobiusHarmonicTree := .branch 37078929 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745728 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745792 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 19728056 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745856 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745920 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 20849488 d273 d274
private def d268 : MobiusHarmonicTree := .branch 40577544 d269 d272
private def d260 : MobiusHarmonicTree := .branch 77656473 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 745984 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746048 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 20449210 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746112 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746176 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 17742570 d281 d282
private def d276 : MobiusHarmonicTree := .branch 38191780 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746240 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746304 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 17101657 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746368 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746432 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 20050095 d288 d289
private def d283 : MobiusHarmonicTree := .branch 37151752 d284 d287
private def d275 : MobiusHarmonicTree := .branch 75343532 d276 d283
private def d259 : MobiusHarmonicTree := .branch 153000005 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746496 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746560 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 20169900 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746624 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746688 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 22015924 d297 d298
private def d292 : MobiusHarmonicTree := .branch 42185824 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746752 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746816 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 22120703 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746880 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 746944 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 21511719 d304 d305
private def d299 : MobiusHarmonicTree := .branch 43632422 d300 d303
private def d291 : MobiusHarmonicTree := .branch 85818246 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747008 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747072 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 22162594 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747136 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747200 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 23078220 d312 d313
private def d307 : MobiusHarmonicTree := .branch 45240814 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747264 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747328 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 22912381 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747392 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747456 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 23404795 d319 d320
private def d314 : MobiusHarmonicTree := .branch 46317176 d315 d318
private def d306 : MobiusHarmonicTree := .branch 91557990 d307 d314
private def d290 : MobiusHarmonicTree := .branch 177376236 d291 d306
private def d258 : MobiusHarmonicTree := .branch 330376241 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747520 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747584 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 22917900 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747648 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747712 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 24127007 d329 d330
private def d324 : MobiusHarmonicTree := .branch 47044907 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747776 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747840 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 23277830 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747904 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 747968 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 22792505 d336 d337
private def d331 : MobiusHarmonicTree := .branch 46070335 d332 d335
private def d323 : MobiusHarmonicTree := .branch 93115242 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748032 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748096 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 23422183 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748160 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748224 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 23550539 d344 d345
private def d339 : MobiusHarmonicTree := .branch 46972722 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748288 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748352 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 23662718 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748416 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748480 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 23856432 d351 d352
private def d346 : MobiusHarmonicTree := .branch 47519150 d347 d350
private def d338 : MobiusHarmonicTree := .branch 94491872 d339 d346
private def d322 : MobiusHarmonicTree := .branch 187607114 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748544 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748608 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 23913782 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748672 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748736 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 23778830 d360 d361
private def d355 : MobiusHarmonicTree := .branch 47692612 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748800 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748864 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 22643726 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748928 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 748992 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 20856134 d367 d368
private def d362 : MobiusHarmonicTree := .branch 43499860 d363 d366
private def d354 : MobiusHarmonicTree := .branch 91192472 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749056 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749120 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 19446888 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749184 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749248 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 19525012 d375 d376
private def d370 : MobiusHarmonicTree := .branch 38971900 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749312 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749376 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 18874448 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749440 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749504 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 18739092 d382 d383
private def d377 : MobiusHarmonicTree := .branch 37613540 d378 d381
private def d369 : MobiusHarmonicTree := .branch 76585440 d370 d377
private def d353 : MobiusHarmonicTree := .branch 167777912 d354 d369
private def d321 : MobiusHarmonicTree := .branch 355385026 d322 d353
private def d257 : MobiusHarmonicTree := .branch 685761267 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749568 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749632 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 22194932 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749696 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749760 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 23680996 d393 d394
private def d388 : MobiusHarmonicTree := .branch 45875928 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749824 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749888 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 23416940 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 749952 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750016 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 23204877 d400 d401
private def d395 : MobiusHarmonicTree := .branch 46621817 d396 d399
private def d387 : MobiusHarmonicTree := .branch 92497745 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750080 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750144 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 24579391 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750208 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750272 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 25546787 d408 d409
private def d403 : MobiusHarmonicTree := .branch 50126178 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750336 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750400 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 27078969 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750464 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750528 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 27155626 d415 d416
private def d410 : MobiusHarmonicTree := .branch 54234595 d411 d414
private def d402 : MobiusHarmonicTree := .branch 104360773 d403 d410
private def d386 : MobiusHarmonicTree := .branch 196858518 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750592 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750656 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 27662581 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750720 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750784 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 26119462 d424 d425
private def d419 : MobiusHarmonicTree := .branch 53782043 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750848 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750912 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 25028300 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 750976 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751040 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 24388922 d431 d432
private def d426 : MobiusHarmonicTree := .branch 49417222 d427 d430
private def d418 : MobiusHarmonicTree := .branch 103199265 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751104 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751168 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 24150499 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751232 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751296 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 22469294 d439 d440
private def d434 : MobiusHarmonicTree := .branch 46619793 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751360 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751424 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 20085946 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751488 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751552 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 20047903 d446 d447
private def d441 : MobiusHarmonicTree := .branch 40133849 d442 d445
private def d433 : MobiusHarmonicTree := .branch 86753642 d434 d441
private def d417 : MobiusHarmonicTree := .branch 189952907 d418 d433
private def d385 : MobiusHarmonicTree := .branch 386811425 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751616 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751680 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 20401076 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751744 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751808 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 19062167 d456 d457
private def d451 : MobiusHarmonicTree := .branch 39463243 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751872 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 751936 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 16974934 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752000 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752064 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 17547767 d463 d464
private def d458 : MobiusHarmonicTree := .branch 34522701 d459 d462
private def d450 : MobiusHarmonicTree := .branch 73985944 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752128 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752192 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 17804045 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752256 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752320 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 16991535 d471 d472
private def d466 : MobiusHarmonicTree := .branch 34795580 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752384 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752448 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 17960112 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752512 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752576 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 18842009 d478 d479
private def d473 : MobiusHarmonicTree := .branch 36802121 d474 d477
private def d465 : MobiusHarmonicTree := .branch 71597701 d466 d473
private def d449 : MobiusHarmonicTree := .branch 145583645 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752640 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752704 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 18049700 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752768 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752832 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 16786023 d487 d488
private def d482 : MobiusHarmonicTree := .branch 34835723 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752896 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 752960 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 16184208 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753024 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753088 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 14997036 d494 d495
private def d489 : MobiusHarmonicTree := .branch 31181244 d490 d493
private def d481 : MobiusHarmonicTree := .branch 66016967 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753152 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753216 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 15808257 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753280 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753344 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 16944551 d502 d503
private def d497 : MobiusHarmonicTree := .branch 32752808 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753408 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753472 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 16473132 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753536 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock091 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753600 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 18009632 d509 d510
private def d504 : MobiusHarmonicTree := .branch 34482764 d505 d508
private def d496 : MobiusHarmonicTree := .branch 67235572 d497 d504
private def d480 : MobiusHarmonicTree := .branch 133252539 d481 d496
private def d448 : MobiusHarmonicTree := .branch 278836184 d449 d480
private def d384 : MobiusHarmonicTree := .branch 665647609 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1351408876 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1816952493 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 737280 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 737280 1816952493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 737280 465543617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 737280 267882542 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 737280 168984431 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 737280 92990108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 737280 50112724 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 737280 27100550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737280 13857951 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737408 13242599 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 737536 23012174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737536 12411987 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737664 10600187 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 737792 42877384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 737792 22433512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737792 11282773 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737920 11150739 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 738048 20443872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738048 10674614 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738176 9769258 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 738304 75994323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 738304 41436016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 738304 19891016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738304 10353981 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738432 9537035 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 738560 21545000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738560 10335484 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738688 11209516 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 738816 34558307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 738816 19686511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738816 10493018 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 738944 9193493 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 739072 14871796 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739072 8189363 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739200 6682433 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 739328 98898111 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 739328 35414295 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 739328 13331274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 739328 7523457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739328 4801343 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739456 2722114 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 739584 5807817 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739584 2996110 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739712 2811707 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 739840 22083021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 739840 9266612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739840 4065422 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 739968 5201190 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 740096 12816409 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740096 5881229 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740224 6935180 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 740352 63483816 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 740352 31269931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 740352 18424623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740352 8847779 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740480 9576844 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 740608 12845308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740608 5593687 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740736 7251621 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 740864 32213885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 740864 16337741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740864 8415215 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 740992 7922526 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 741120 15876144 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 741120 8288160 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 741248 7587984 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 741376 197661075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 741376 46457588 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 741376 23842713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 741376 16178021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 741376 11095417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 741376 6728911 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 741504 4366506 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 741632 5082604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 741632 2083151 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 741760 2999453 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 741888 7664692 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 741888 4029655 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 741888 1842522 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742016 2187133 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 742144 3635037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742144 2301346 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742272 1333691 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 742400 22614875 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 742400 10257207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 742400 3559516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742400 1530085 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742528 2029431 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 742656 6697691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742656 2286268 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742784 4411423 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 742912 12357668 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 742912 8003879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 742912 4640883 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743040 3362996 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 743168 4353789 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743168 2462304 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743296 1891485 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 743424 151203487 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 743424 42402246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 743424 12190648 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 743424 5122818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743424 2411667 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743552 2711151 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 743680 7067830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743680 3735213 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743808 3332617 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 743936 30211598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 743936 12354997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 743936 5040347 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744064 7314650 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 744192 17856601 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744192 8321087 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744320 9535514 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 744448 108801241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 744448 53082000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 744448 24663440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744448 10503545 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744576 14159895 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 744704 28418560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744704 13812422 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744832 14606138 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 744960 55719241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 744960 26903184 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 744960 14180856 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745088 12722328 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 745216 28816057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745216 13063566 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745344 15752491 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 745472 1351408876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 745472 685761267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 745472 330376241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 745472 153000005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 745472 77656473 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 745472 37078929 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745472 18233892 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745600 18845037 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 745728 40577544 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745728 19728056 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745856 20849488 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 745984 75343532 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 745984 38191780 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 745984 20449210 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 746112 17742570 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 746240 37151752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 746240 17101657 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 746368 20050095 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 746496 177376236 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 746496 85818246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 746496 42185824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 746496 20169900 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 746624 22015924 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 746752 43632422 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 746752 22120703 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 746880 21511719 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 747008 91557990 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 747008 45240814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747008 22162594 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747136 23078220 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 747264 46317176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747264 22912381 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747392 23404795 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 747520 355385026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 747520 187607114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 747520 93115242 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 747520 47044907 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747520 22917900 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747648 24127007 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 747776 46070335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747776 23277830 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 747904 22792505 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 748032 94491872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 748032 46972722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748032 23422183 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748160 23550539 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 748288 47519150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748288 23662718 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748416 23856432 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 748544 167777912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 748544 91192472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 748544 47692612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748544 23913782 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748672 23778830 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 748800 43499860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748800 22643726 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 748928 20856134 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 749056 76585440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 749056 38971900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749056 19446888 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749184 19525012 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 749312 37613540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749312 18874448 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749440 18739092 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 749568 665647609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 749568 386811425 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 749568 196858518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 749568 92497745 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 749568 45875928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749568 22194932 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749696 23680996 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 749824 46621817 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749824 23416940 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 749952 23204877 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 750080 104360773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 750080 50126178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750080 24579391 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750208 25546787 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 750336 54234595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750336 27078969 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750464 27155626 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 750592 189952907 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 750592 103199265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 750592 53782043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750592 27662581 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750720 26119462 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 750848 49417222 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750848 25028300 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 750976 24388922 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 751104 86753642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 751104 46619793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 751104 24150499 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 751232 22469294 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 751360 40133849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 751360 20085946 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 751488 20047903 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 751616 278836184 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 751616 145583645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 751616 73985944 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 751616 39463243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 751616 20401076 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 751744 19062167 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 751872 34522701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 751872 16974934 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752000 17547767 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 752128 71597701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 752128 34795580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752128 17804045 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752256 16991535 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 752384 36802121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752384 17960112 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752512 18842009 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 752640 133252539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 752640 66016967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 752640 34835723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752640 18049700 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752768 16786023 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 752896 31181244 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 752896 16184208 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753024 14997036 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 753152 67235572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 753152 32752808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753152 15808257 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753280 16944551 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 753408 34482764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753408 16473132 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753536 18009632 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 737280 (MobiusHarmonicTree.branch 1816952493 mobiusHarmonicBlock090 mobiusHarmonicBlock091) = true := Helfgott.combined

#print axioms solution
