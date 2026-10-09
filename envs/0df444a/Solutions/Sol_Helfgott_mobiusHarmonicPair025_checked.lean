-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair025_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:26:21.071988+00:00
-- url     : https://prove2.me/submissions/04adbb25-efe3-4634-9eee-ca72231e9606

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409600 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409664 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 25755336 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409728 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409792 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 26371939 d11 d12
private def d6 : MobiusHarmonicTree := .branch 52127275 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409856 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409920 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 27859269 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409984 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410048 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 26377459 d18 d19
private def d13 : MobiusHarmonicTree := .branch 54236728 d14 d17
private def d5 : MobiusHarmonicTree := .branch 106364003 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410112 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410176 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 28838884 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410240 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410304 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 32778097 d26 d27
private def d21 : MobiusHarmonicTree := .branch 61616981 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410368 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410432 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 35011956 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410496 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410560 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 35166665 d33 d34
private def d28 : MobiusHarmonicTree := .branch 70178621 d29 d32
private def d20 : MobiusHarmonicTree := .branch 131795602 d21 d28
private def d4 : MobiusHarmonicTree := .branch 238159605 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410624 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410688 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 38050860 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410752 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410816 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 36527343 d42 d43
private def d37 : MobiusHarmonicTree := .branch 74578203 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410880 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 410944 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 40981259 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411008 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411072 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 39939615 d49 d50
private def d44 : MobiusHarmonicTree := .branch 80920874 d45 d48
private def d36 : MobiusHarmonicTree := .branch 155499077 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411136 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411200 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 39662092 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411264 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411328 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 40546763 d57 d58
private def d52 : MobiusHarmonicTree := .branch 80208855 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411392 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411456 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 38721220 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411520 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411584 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 38969074 d64 d65
private def d59 : MobiusHarmonicTree := .branch 77690294 d60 d63
private def d51 : MobiusHarmonicTree := .branch 157899149 d52 d59
private def d35 : MobiusHarmonicTree := .branch 313398226 d36 d51
private def d3 : MobiusHarmonicTree := .branch 551557831 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411648 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411712 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 37465799 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411776 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411840 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 32471496 d74 d75
private def d69 : MobiusHarmonicTree := .branch 69937295 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411904 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 411968 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 35214000 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412032 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412096 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 34572149 d81 d82
private def d76 : MobiusHarmonicTree := .branch 69786149 d77 d80
private def d68 : MobiusHarmonicTree := .branch 139723444 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412160 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412224 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 33760966 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412288 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412352 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 33391413 d89 d90
private def d84 : MobiusHarmonicTree := .branch 67152379 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412416 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412480 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 37943659 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412544 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412608 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 40479338 d96 d97
private def d91 : MobiusHarmonicTree := .branch 78422997 d92 d95
private def d83 : MobiusHarmonicTree := .branch 145575376 d84 d91
private def d67 : MobiusHarmonicTree := .branch 285298820 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412672 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412736 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 41539854 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412800 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412864 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 45073109 d105 d106
private def d100 : MobiusHarmonicTree := .branch 86612963 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412928 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 412992 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 45184869 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413056 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413120 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 46686348 d112 d113
private def d107 : MobiusHarmonicTree := .branch 91871217 d108 d111
private def d99 : MobiusHarmonicTree := .branch 178484180 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413184 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413248 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 47489683 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413312 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413376 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 47854896 d120 d121
private def d115 : MobiusHarmonicTree := .branch 95344579 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413440 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413504 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 45264471 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413568 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413632 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 47580953 d127 d128
private def d122 : MobiusHarmonicTree := .branch 92845424 d123 d126
private def d114 : MobiusHarmonicTree := .branch 188190003 d115 d122
private def d98 : MobiusHarmonicTree := .branch 366674183 d99 d114
private def d66 : MobiusHarmonicTree := .branch 651973003 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1203530834 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413696 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413760 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 46964602 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413824 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413888 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 47972023 d138 d139
private def d133 : MobiusHarmonicTree := .branch 94936625 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 413952 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414016 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 46539445 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414080 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414144 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 44960327 d145 d146
private def d140 : MobiusHarmonicTree := .branch 91499772 d141 d144
private def d132 : MobiusHarmonicTree := .branch 186436397 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414208 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414272 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 46143612 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414336 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414400 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 46110322 d153 d154
private def d148 : MobiusHarmonicTree := .branch 92253934 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414464 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414528 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 45779800 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414592 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414656 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 47659033 d160 d161
private def d155 : MobiusHarmonicTree := .branch 93438833 d156 d159
private def d147 : MobiusHarmonicTree := .branch 185692767 d148 d155
private def d131 : MobiusHarmonicTree := .branch 372129164 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414720 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414784 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 42468193 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414848 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414912 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 41681156 d169 d170
private def d164 : MobiusHarmonicTree := .branch 84149349 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 414976 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415040 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 44178970 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415104 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415168 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 42778017 d176 d177
private def d171 : MobiusHarmonicTree := .branch 86956987 d172 d175
private def d163 : MobiusHarmonicTree := .branch 171106336 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415232 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415296 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 42437272 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415360 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415424 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 44751970 d184 d185
private def d179 : MobiusHarmonicTree := .branch 87189242 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415488 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415552 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 44661177 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415616 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415680 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 44505501 d191 d192
private def d186 : MobiusHarmonicTree := .branch 89166678 d187 d190
private def d178 : MobiusHarmonicTree := .branch 176355920 d179 d186
private def d162 : MobiusHarmonicTree := .branch 347462256 d163 d178
private def d130 : MobiusHarmonicTree := .branch 719591420 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415744 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415808 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 46627439 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415872 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 415936 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 46899121 d201 d202
private def d196 : MobiusHarmonicTree := .branch 93526560 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416000 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416064 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 45363307 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416128 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416192 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 48677147 d208 d209
private def d203 : MobiusHarmonicTree := .branch 94040454 d204 d207
private def d195 : MobiusHarmonicTree := .branch 187567014 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416256 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416320 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 48445992 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416384 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416448 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 47485052 d216 d217
private def d211 : MobiusHarmonicTree := .branch 95931044 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416512 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416576 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 47640912 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416640 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416704 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 47040664 d223 d224
private def d218 : MobiusHarmonicTree := .branch 94681576 d219 d222
private def d210 : MobiusHarmonicTree := .branch 190612620 d211 d218
private def d194 : MobiusHarmonicTree := .branch 378179634 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416768 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416832 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 51963461 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416896 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 416960 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 52343326 d232 d233
private def d227 : MobiusHarmonicTree := .branch 104306787 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417024 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417088 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 51670257 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417152 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417216 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 49782531 d239 d240
private def d234 : MobiusHarmonicTree := .branch 101452788 d235 d238
private def d226 : MobiusHarmonicTree := .branch 205759575 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417280 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417344 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 52330972 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417408 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417472 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 51316187 d247 d248
private def d242 : MobiusHarmonicTree := .branch 103647159 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417536 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417600 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 50522184 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417664 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock050 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417728 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 48622804 d254 d255
private def d249 : MobiusHarmonicTree := .branch 99144988 d250 d253
private def d241 : MobiusHarmonicTree := .branch 202792147 d242 d249
private def d225 : MobiusHarmonicTree := .branch 408551722 d226 d241
private def d193 : MobiusHarmonicTree := .branch 786731356 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1506322776 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2709853610 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417792 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417856 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 47839458 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417920 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 417984 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 50243722 d266 d267
private def d261 : MobiusHarmonicTree := .branch 98083180 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418048 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418112 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 53409144 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418176 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418240 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 50889720 d273 d274
private def d268 : MobiusHarmonicTree := .branch 104298864 d269 d272
private def d260 : MobiusHarmonicTree := .branch 202382044 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418304 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418368 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 46277638 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418432 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418496 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 46174864 d281 d282
private def d276 : MobiusHarmonicTree := .branch 92452502 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418560 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418624 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 50551427 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418688 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418752 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 52303152 d288 d289
private def d283 : MobiusHarmonicTree := .branch 102854579 d284 d287
private def d275 : MobiusHarmonicTree := .branch 195307081 d276 d283
private def d259 : MobiusHarmonicTree := .branch 397689125 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418816 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418880 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 50016877 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 418944 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419008 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 46144945 d297 d298
private def d292 : MobiusHarmonicTree := .branch 96161822 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419072 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419136 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 44708757 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419200 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419264 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 44473294 d304 d305
private def d299 : MobiusHarmonicTree := .branch 89182051 d300 d303
private def d291 : MobiusHarmonicTree := .branch 185343873 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419328 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419392 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 45971400 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419456 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419520 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 42923078 d312 d313
private def d307 : MobiusHarmonicTree := .branch 88894478 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419584 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419648 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 40162260 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419712 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419776 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 40012075 d319 d320
private def d314 : MobiusHarmonicTree := .branch 80174335 d315 d318
private def d306 : MobiusHarmonicTree := .branch 169068813 d307 d314
private def d290 : MobiusHarmonicTree := .branch 354412686 d291 d306
private def d258 : MobiusHarmonicTree := .branch 752101811 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419840 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419904 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 39606710 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 419968 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420032 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 42439709 d329 d330
private def d324 : MobiusHarmonicTree := .branch 82046419 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420096 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420160 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 44138040 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420224 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420288 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 44369699 d336 d337
private def d331 : MobiusHarmonicTree := .branch 88507739 d332 d335
private def d323 : MobiusHarmonicTree := .branch 170554158 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420352 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420416 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 43321502 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420480 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420544 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 44366356 d344 d345
private def d339 : MobiusHarmonicTree := .branch 87687858 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420608 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420672 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 50550149 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420736 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420800 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 49741086 d351 d352
private def d346 : MobiusHarmonicTree := .branch 100291235 d347 d350
private def d338 : MobiusHarmonicTree := .branch 187979093 d339 d346
private def d322 : MobiusHarmonicTree := .branch 358533251 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420864 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420928 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 47566468 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 420992 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421056 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 46834761 d360 d361
private def d355 : MobiusHarmonicTree := .branch 94401229 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421120 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421184 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 46932084 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421248 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421312 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 46118091 d367 d368
private def d362 : MobiusHarmonicTree := .branch 93050175 d363 d366
private def d354 : MobiusHarmonicTree := .branch 187451404 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421376 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421440 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 41619455 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421504 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421568 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 43399830 d375 d376
private def d370 : MobiusHarmonicTree := .branch 85019285 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421632 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421696 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 47237919 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421760 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421824 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 48617481 d382 d383
private def d377 : MobiusHarmonicTree := .branch 95855400 d378 d381
private def d369 : MobiusHarmonicTree := .branch 180874685 d370 d377
private def d353 : MobiusHarmonicTree := .branch 368326089 d354 d369
private def d321 : MobiusHarmonicTree := .branch 726859340 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1478961151 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421888 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 421952 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 51316381 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422016 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422080 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 53087227 d393 d394
private def d388 : MobiusHarmonicTree := .branch 104403608 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422144 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422208 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 54686418 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422272 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422336 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 54946777 d400 d401
private def d395 : MobiusHarmonicTree := .branch 109633195 d396 d399
private def d387 : MobiusHarmonicTree := .branch 214036803 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422400 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422464 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 57834562 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422528 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422592 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 56409252 d408 d409
private def d403 : MobiusHarmonicTree := .branch 114243814 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422656 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422720 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 57936774 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422784 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422848 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 56129207 d415 d416
private def d410 : MobiusHarmonicTree := .branch 114065981 d411 d414
private def d402 : MobiusHarmonicTree := .branch 228309795 d403 d410
private def d386 : MobiusHarmonicTree := .branch 442346598 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422912 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 422976 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 52863692 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423040 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423104 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 48657229 d424 d425
private def d419 : MobiusHarmonicTree := .branch 101520921 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423168 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423232 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 49845135 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423296 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423360 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 49112009 d431 d432
private def d426 : MobiusHarmonicTree := .branch 98957144 d427 d430
private def d418 : MobiusHarmonicTree := .branch 200478065 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423424 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423488 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 44506807 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423552 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423616 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 44405818 d439 d440
private def d434 : MobiusHarmonicTree := .branch 88912625 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423680 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423744 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 44803157 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423808 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423872 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 40965452 d446 d447
private def d441 : MobiusHarmonicTree := .branch 85768609 d442 d445
private def d433 : MobiusHarmonicTree := .branch 174681234 d434 d441
private def d417 : MobiusHarmonicTree := .branch 375159299 d418 d433
private def d385 : MobiusHarmonicTree := .branch 817505897 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 423936 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424000 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 40063785 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424064 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424128 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 38219836 d456 d457
private def d451 : MobiusHarmonicTree := .branch 78283621 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424192 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424256 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 37017861 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424320 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424384 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 36349231 d463 d464
private def d458 : MobiusHarmonicTree := .branch 73367092 d459 d462
private def d450 : MobiusHarmonicTree := .branch 151650713 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424448 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424512 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 36432498 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424576 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424640 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 35366537 d471 d472
private def d466 : MobiusHarmonicTree := .branch 71799035 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424704 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424768 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 34875606 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424832 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424896 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 34523838 d478 d479
private def d473 : MobiusHarmonicTree := .branch 69399444 d474 d477
private def d465 : MobiusHarmonicTree := .branch 141198479 d466 d473
private def d449 : MobiusHarmonicTree := .branch 292849192 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 424960 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425024 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 37362641 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425088 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425152 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 39188328 d487 d488
private def d482 : MobiusHarmonicTree := .branch 76550969 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425216 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425280 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 39139004 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425344 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425408 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 39726682 d494 d495
private def d489 : MobiusHarmonicTree := .branch 78865686 d490 d493
private def d481 : MobiusHarmonicTree := .branch 155416655 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425472 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425536 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 36941776 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425600 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425664 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 37769307 d502 d503
private def d497 : MobiusHarmonicTree := .branch 74711083 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425728 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425792 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 38530691 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425856 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock051 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425920 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 36955421 d509 d510
private def d504 : MobiusHarmonicTree := .branch 75486112 d505 d508
private def d496 : MobiusHarmonicTree := .branch 150197195 d497 d504
private def d480 : MobiusHarmonicTree := .branch 305613850 d481 d496
private def d448 : MobiusHarmonicTree := .branch 598463042 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1415968939 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2894930090 d257 d384
private def d0 : MobiusHarmonicTree := .branch 5604783700 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 409600 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 409600 5604783700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 409600 2709853610 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 409600 1203530834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 409600 551557831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 409600 238159605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 409600 106364003 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 409600 52127275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409600 25755336 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409728 26371939 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 409856 54236728 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409856 27859269 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409984 26377459 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 410112 131795602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 410112 61616981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 410112 28838884 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 410240 32778097 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 410368 70178621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 410368 35011956 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 410496 35166665 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 410624 313398226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 410624 155499077 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 410624 74578203 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 410624 38050860 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 410752 36527343 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 410880 80920874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 410880 40981259 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411008 39939615 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 411136 157899149 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 411136 80208855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411136 39662092 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411264 40546763 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 411392 77690294 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411392 38721220 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411520 38969074 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 411648 651973003 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 411648 285298820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 411648 139723444 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 411648 69937295 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411648 37465799 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411776 32471496 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 411904 69786149 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 411904 35214000 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412032 34572149 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 412160 145575376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 412160 67152379 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412160 33760966 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412288 33391413 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 412416 78422997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412416 37943659 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412544 40479338 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 412672 366674183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 412672 178484180 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 412672 86612963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412672 41539854 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412800 45073109 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 412928 91871217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 412928 45184869 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413056 46686348 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 413184 188190003 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 413184 95344579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413184 47489683 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413312 47854896 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 413440 92845424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413440 45264471 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413568 47580953 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 413696 1506322776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 413696 719591420 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 413696 372129164 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 413696 186436397 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 413696 94936625 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413696 46964602 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413824 47972023 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 413952 91499772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 413952 46539445 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414080 44960327 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 414208 185692767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 414208 92253934 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414208 46143612 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414336 46110322 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 414464 93438833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414464 45779800 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414592 47659033 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 414720 347462256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 414720 171106336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 414720 84149349 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414720 42468193 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414848 41681156 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 414976 86956987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 414976 44178970 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 415104 42778017 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 415232 176355920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 415232 87189242 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 415232 42437272 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 415360 44751970 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 415488 89166678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 415488 44661177 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 415616 44505501 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 415744 786731356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 415744 378179634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 415744 187567014 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 415744 93526560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 415744 46627439 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 415872 46899121 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 416000 94040454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416000 45363307 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416128 48677147 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 416256 190612620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 416256 95931044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416256 48445992 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416384 47485052 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 416512 94681576 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416512 47640912 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416640 47040664 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 416768 408551722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 416768 205759575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 416768 104306787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416768 51963461 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 416896 52343326 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 417024 101452788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417024 51670257 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417152 49782531 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 417280 202792147 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 417280 103647159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417280 52330972 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417408 51316187 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 417536 99144988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417536 50522184 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417664 48622804 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 417792 2894930090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 417792 1478961151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 417792 752101811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 417792 397689125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 417792 202382044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 417792 98083180 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417792 47839458 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 417920 50243722 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 418048 104298864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418048 53409144 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418176 50889720 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 418304 195307081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 418304 92452502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418304 46277638 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418432 46174864 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 418560 102854579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418560 50551427 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418688 52303152 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 418816 354412686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 418816 185343873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 418816 96161822 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418816 50016877 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 418944 46144945 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 419072 89182051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419072 44708757 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419200 44473294 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 419328 169068813 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 419328 88894478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419328 45971400 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419456 42923078 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 419584 80174335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419584 40162260 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419712 40012075 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 419840 726859340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 419840 358533251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 419840 170554158 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 419840 82046419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419840 39606710 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 419968 42439709 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 420096 88507739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420096 44138040 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420224 44369699 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 420352 187979093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 420352 87687858 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420352 43321502 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420480 44366356 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 420608 100291235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420608 50550149 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420736 49741086 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 420864 368326089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 420864 187451404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 420864 94401229 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420864 47566468 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 420992 46834761 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 421120 93050175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 421120 46932084 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 421248 46118091 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 421376 180874685 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 421376 85019285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 421376 41619455 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 421504 43399830 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 421632 95855400 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 421632 47237919 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 421760 48617481 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 421888 1415968939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 421888 817505897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 421888 442346598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 421888 214036803 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 421888 104403608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 421888 51316381 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422016 53087227 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 422144 109633195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422144 54686418 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422272 54946777 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 422400 228309795 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 422400 114243814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422400 57834562 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422528 56409252 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 422656 114065981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422656 57936774 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422784 56129207 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 422912 375159299 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 422912 200478065 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 422912 101520921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 422912 52863692 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423040 48657229 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 423168 98957144 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423168 49845135 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423296 49112009 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 423424 174681234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 423424 88912625 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423424 44506807 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423552 44405818 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 423680 85768609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423680 44803157 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423808 40965452 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 423936 598463042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 423936 292849192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 423936 151650713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 423936 78283621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 423936 40063785 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424064 38219836 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 424192 73367092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424192 37017861 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424320 36349231 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 424448 141198479 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 424448 71799035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424448 36432498 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424576 35366537 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 424704 69399444 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424704 34875606 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424832 34523838 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 424960 305613850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 424960 155416655 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 424960 76550969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 424960 37362641 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425088 39188328 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 425216 78865686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425216 39139004 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425344 39726682 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 425472 150197195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 425472 74711083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425472 36941776 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425600 37769307 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 425728 75486112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425728 38530691 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425856 36955421 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 409600 (MobiusHarmonicTree.branch 5604783700 mobiusHarmonicBlock050 mobiusHarmonicBlock051) = true := Helfgott.combined

#print axioms solution
