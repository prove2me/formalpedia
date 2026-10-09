-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair007_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:17:35.68285+00:00
-- url     : https://prove2.me/submissions/1247447c-52e6-448b-9dc6-fe631ce26a98

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114688 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114752 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 105045514 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114816 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114880 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 99260492 d11 d12
private def d6 : MobiusHarmonicTree := .branch 204306006 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114944 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115008 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 104514407 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115072 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115136 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 105718661 d18 d19
private def d13 : MobiusHarmonicTree := .branch 210233068 d14 d17
private def d5 : MobiusHarmonicTree := .branch 414539074 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115200 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115264 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 100831034 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115328 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115392 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 98351044 d26 d27
private def d21 : MobiusHarmonicTree := .branch 199182078 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115456 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115520 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 106423907 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115584 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115648 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 104653224 d33 d34
private def d28 : MobiusHarmonicTree := .branch 211077131 d29 d32
private def d20 : MobiusHarmonicTree := .branch 410259209 d21 d28
private def d4 : MobiusHarmonicTree := .branch 824798283 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115712 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115776 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 104203511 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115840 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115904 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 91724523 d42 d43
private def d37 : MobiusHarmonicTree := .branch 195928034 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 115968 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116032 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 86002570 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116096 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116160 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 88404280 d49 d50
private def d44 : MobiusHarmonicTree := .branch 174406850 d45 d48
private def d36 : MobiusHarmonicTree := .branch 370334884 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116224 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116288 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 92934000 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116352 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116416 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 90906477 d57 d58
private def d52 : MobiusHarmonicTree := .branch 183840477 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116480 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116544 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 98924107 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116608 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116672 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 105355211 d64 d65
private def d59 : MobiusHarmonicTree := .branch 204279318 d60 d63
private def d51 : MobiusHarmonicTree := .branch 388119795 d52 d59
private def d35 : MobiusHarmonicTree := .branch 758454679 d36 d51
private def d3 : MobiusHarmonicTree := .branch 1583252962 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116736 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116800 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 117285587 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116864 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116928 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 120810735 d74 d75
private def d69 : MobiusHarmonicTree := .branch 238096322 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 116992 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117056 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 101056579 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117120 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117184 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 93699338 d81 d82
private def d76 : MobiusHarmonicTree := .branch 194755917 d77 d80
private def d68 : MobiusHarmonicTree := .branch 432852239 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117248 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117312 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 91968127 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117376 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117440 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 92320254 d89 d90
private def d84 : MobiusHarmonicTree := .branch 184288381 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117504 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117568 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 88051877 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117632 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117696 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 82653884 d96 d97
private def d91 : MobiusHarmonicTree := .branch 170705761 d92 d95
private def d83 : MobiusHarmonicTree := .branch 354994142 d84 d91
private def d67 : MobiusHarmonicTree := .branch 787846381 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117760 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117824 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 89641409 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117888 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 117952 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 94725482 d105 d106
private def d100 : MobiusHarmonicTree := .branch 184366891 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118016 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118080 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 96290129 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118144 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118208 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 102997069 d112 d113
private def d107 : MobiusHarmonicTree := .branch 199287198 d108 d111
private def d99 : MobiusHarmonicTree := .branch 383654089 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118272 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118336 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 100889619 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118400 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118464 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 111721331 d120 d121
private def d115 : MobiusHarmonicTree := .branch 212610950 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118528 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118592 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 111940110 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118656 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118720 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 107285221 d127 d128
private def d122 : MobiusHarmonicTree := .branch 219225331 d123 d126
private def d114 : MobiusHarmonicTree := .branch 431836281 d115 d122
private def d98 : MobiusHarmonicTree := .branch 815490370 d99 d114
private def d66 : MobiusHarmonicTree := .branch 1603336751 d67 d98
private def d2 : MobiusHarmonicTree := .branch 3186589713 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118784 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118848 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 118924357 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118912 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 118976 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 120360066 d138 d139
private def d133 : MobiusHarmonicTree := .branch 239284423 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119040 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119104 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 122296048 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119168 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119232 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 120699158 d145 d146
private def d140 : MobiusHarmonicTree := .branch 242995206 d141 d144
private def d132 : MobiusHarmonicTree := .branch 482279629 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119296 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119360 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 118507405 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119424 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119488 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 131978801 d153 d154
private def d148 : MobiusHarmonicTree := .branch 250486206 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119552 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119616 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 133679179 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119680 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119744 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 126212240 d160 d161
private def d155 : MobiusHarmonicTree := .branch 259891419 d156 d159
private def d147 : MobiusHarmonicTree := .branch 510377625 d148 d155
private def d131 : MobiusHarmonicTree := .branch 992657254 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119808 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119872 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 116901398 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 119936 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120000 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 112217076 d169 d170
private def d164 : MobiusHarmonicTree := .branch 229118474 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120064 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120128 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 109990899 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120192 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120256 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 112028253 d176 d177
private def d171 : MobiusHarmonicTree := .branch 222019152 d172 d175
private def d163 : MobiusHarmonicTree := .branch 451137626 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120320 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120384 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 120681838 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120448 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120512 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 130948641 d184 d185
private def d179 : MobiusHarmonicTree := .branch 251630479 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120576 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120640 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 130339864 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120704 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120768 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 119296135 d191 d192
private def d186 : MobiusHarmonicTree := .branch 249635999 d187 d190
private def d178 : MobiusHarmonicTree := .branch 501266478 d179 d186
private def d162 : MobiusHarmonicTree := .branch 952404104 d163 d178
private def d130 : MobiusHarmonicTree := .branch 1945061358 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120832 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120896 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 110113991 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 120960 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121024 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 85075576 d201 d202
private def d196 : MobiusHarmonicTree := .branch 195189567 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121088 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121152 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 75790087 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121216 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121280 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 81027679 d208 d209
private def d203 : MobiusHarmonicTree := .branch 156817766 d204 d207
private def d195 : MobiusHarmonicTree := .branch 352007333 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121344 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121408 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 72418127 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121472 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121536 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 66828630 d216 d217
private def d211 : MobiusHarmonicTree := .branch 139246757 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121600 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121664 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 53730895 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121728 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121792 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 55412576 d223 d224
private def d218 : MobiusHarmonicTree := .branch 109143471 d219 d222
private def d210 : MobiusHarmonicTree := .branch 248390228 d211 d218
private def d194 : MobiusHarmonicTree := .branch 600397561 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121856 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121920 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 70054460 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 121984 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122048 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 60682199 d232 d233
private def d227 : MobiusHarmonicTree := .branch 130736659 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122112 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122176 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 53981595 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122240 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122304 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 43556526 d239 d240
private def d234 : MobiusHarmonicTree := .branch 97538121 d235 d238
private def d226 : MobiusHarmonicTree := .branch 228274780 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122368 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122432 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 39466792 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122496 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122560 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 41041839 d247 d248
private def d242 : MobiusHarmonicTree := .branch 80508631 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122624 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122688 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 38463733 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122752 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock014 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122816 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 42828049 d254 d255
private def d249 : MobiusHarmonicTree := .branch 81291782 d250 d253
private def d241 : MobiusHarmonicTree := .branch 161800413 d242 d249
private def d225 : MobiusHarmonicTree := .branch 390075193 d226 d241
private def d193 : MobiusHarmonicTree := .branch 990472754 d194 d225
private def d129 : MobiusHarmonicTree := .branch 2935534112 d130 d193
private def d1 : MobiusHarmonicTree := .branch 6122123825 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122880 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 122944 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 42067788 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123008 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123072 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 42885204 d266 d267
private def d261 : MobiusHarmonicTree := .branch 84952992 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123136 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123200 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 47183869 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123264 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123328 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 40866695 d273 d274
private def d268 : MobiusHarmonicTree := .branch 88050564 d269 d272
private def d260 : MobiusHarmonicTree := .branch 173003556 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123392 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123456 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 43992645 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123520 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123584 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 27537402 d281 d282
private def d276 : MobiusHarmonicTree := .branch 71530047 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123648 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123712 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 24184805 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123776 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123840 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 27115718 d288 d289
private def d283 : MobiusHarmonicTree := .branch 51300523 d284 d287
private def d275 : MobiusHarmonicTree := .branch 122830570 d276 d283
private def d259 : MobiusHarmonicTree := .branch 295834126 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123904 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 123968 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 27330206 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124032 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124096 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 35408225 d297 d298
private def d292 : MobiusHarmonicTree := .branch 62738431 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124160 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124224 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 35258644 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124288 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124352 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 26684063 d304 d305
private def d299 : MobiusHarmonicTree := .branch 61942707 d300 d303
private def d291 : MobiusHarmonicTree := .branch 124681138 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124416 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124480 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 20662905 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124544 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124608 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 21658859 d312 d313
private def d307 : MobiusHarmonicTree := .branch 42321764 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124672 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124736 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 19482324 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124800 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124864 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 17914389 d319 d320
private def d314 : MobiusHarmonicTree := .branch 37396713 d315 d318
private def d306 : MobiusHarmonicTree := .branch 79718477 d307 d314
private def d290 : MobiusHarmonicTree := .branch 204399615 d291 d306
private def d258 : MobiusHarmonicTree := .branch 500233741 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124928 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 124992 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 28354124 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125056 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125120 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 19342690 d329 d330
private def d324 : MobiusHarmonicTree := .branch 47696814 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125184 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125248 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 14755362 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125312 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125376 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 14236885 d336 d337
private def d331 : MobiusHarmonicTree := .branch 28992247 d332 d335
private def d323 : MobiusHarmonicTree := .branch 76689061 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125440 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125504 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 10820679 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125568 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125632 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 7571207 d344 d345
private def d339 : MobiusHarmonicTree := .branch 18391886 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125696 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125760 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 2981854 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125824 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125888 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 8300549 d351 d352
private def d346 : MobiusHarmonicTree := .branch 11282403 d347 d350
private def d338 : MobiusHarmonicTree := .branch 29674289 d339 d346
private def d322 : MobiusHarmonicTree := .branch 106363350 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 125952 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126016 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 12807603 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126080 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126144 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 7270979 d360 d361
private def d355 : MobiusHarmonicTree := .branch 20078582 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126208 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126272 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 11774692 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126336 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126400 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 16028064 d367 d368
private def d362 : MobiusHarmonicTree := .branch 27802756 d363 d366
private def d354 : MobiusHarmonicTree := .branch 47881338 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126464 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126528 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 10527132 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126592 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126656 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 18158500 d375 d376
private def d370 : MobiusHarmonicTree := .branch 28685632 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126720 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126784 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 17880170 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126848 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126912 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 24607283 d382 d383
private def d377 : MobiusHarmonicTree := .branch 42487453 d378 d381
private def d369 : MobiusHarmonicTree := .branch 71173085 d370 d377
private def d353 : MobiusHarmonicTree := .branch 119054423 d354 d369
private def d321 : MobiusHarmonicTree := .branch 225417773 d322 d353
private def d257 : MobiusHarmonicTree := .branch 725651514 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 126976 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127040 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 37128076 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127104 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127168 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 47236698 d393 d394
private def d388 : MobiusHarmonicTree := .branch 84364774 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127232 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127296 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 50842114 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127360 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127424 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 60875057 d400 d401
private def d395 : MobiusHarmonicTree := .branch 111717171 d396 d399
private def d387 : MobiusHarmonicTree := .branch 196081945 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127488 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127552 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 67266413 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127616 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127680 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 71843742 d408 d409
private def d403 : MobiusHarmonicTree := .branch 139110155 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127744 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127808 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 72836071 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127872 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 127936 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 64040580 d415 d416
private def d410 : MobiusHarmonicTree := .branch 136876651 d411 d414
private def d402 : MobiusHarmonicTree := .branch 275986806 d403 d410
private def d386 : MobiusHarmonicTree := .branch 472068751 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128000 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128064 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 66412116 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128128 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128192 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 73351643 d424 d425
private def d419 : MobiusHarmonicTree := .branch 139763759 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128256 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128320 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 64074387 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128384 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128448 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 60025449 d431 d432
private def d426 : MobiusHarmonicTree := .branch 124099836 d427 d430
private def d418 : MobiusHarmonicTree := .branch 263863595 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128512 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128576 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 56993997 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128640 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128704 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 55010371 d439 d440
private def d434 : MobiusHarmonicTree := .branch 112004368 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128768 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128832 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 60583153 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128896 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128960 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 56073672 d446 d447
private def d441 : MobiusHarmonicTree := .branch 116656825 d442 d445
private def d433 : MobiusHarmonicTree := .branch 228661193 d434 d441
private def d417 : MobiusHarmonicTree := .branch 492524788 d418 d433
private def d385 : MobiusHarmonicTree := .branch 964593539 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129024 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129088 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 38827980 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129152 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129216 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 28317407 d456 d457
private def d451 : MobiusHarmonicTree := .branch 67145387 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129280 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129344 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 26409915 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129408 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129472 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 15920261 d463 d464
private def d458 : MobiusHarmonicTree := .branch 42330176 d459 d462
private def d450 : MobiusHarmonicTree := .branch 109475563 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129536 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129600 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 2708434 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129664 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129728 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 8787199 d471 d472
private def d466 : MobiusHarmonicTree := .branch 11495633 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129792 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129856 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 6984667 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129920 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 129984 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 5493406 d478 d479
private def d473 : MobiusHarmonicTree := .branch 12478073 d474 d477
private def d465 : MobiusHarmonicTree := .branch 23973706 d466 d473
private def d449 : MobiusHarmonicTree := .branch 133449269 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130048 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130112 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 10536663 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130176 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130240 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 3324979 d487 d488
private def d482 : MobiusHarmonicTree := .branch 13861642 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130304 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130368 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 6181447 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130432 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130496 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 22459641 d494 d495
private def d489 : MobiusHarmonicTree := .branch 28641088 d490 d493
private def d481 : MobiusHarmonicTree := .branch 42502730 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130560 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130624 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 24023202 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130688 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130752 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 21094612 d502 d503
private def d497 : MobiusHarmonicTree := .branch 45117814 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130816 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130880 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 14067447 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 130944 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock015 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131008 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 12372779 d509 d510
private def d504 : MobiusHarmonicTree := .branch 26440226 d505 d508
private def d496 : MobiusHarmonicTree := .branch 71558040 d497 d504
private def d480 : MobiusHarmonicTree := .branch 114060770 d481 d496
private def d448 : MobiusHarmonicTree := .branch 247510039 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1212103578 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1937755092 d257 d384
private def d0 : MobiusHarmonicTree := .branch 8059878917 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 114688 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 114688 8059878917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 114688 6122123825 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 114688 3186589713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 114688 1583252962 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 114688 824798283 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 114688 414539074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 114688 204306006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114688 105045514 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114816 99260492 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 114944 210233068 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114944 104514407 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115072 105718661 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 115200 410259209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 115200 199182078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115200 100831034 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115328 98351044 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 115456 211077131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115456 106423907 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115584 104653224 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 115712 758454679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 115712 370334884 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 115712 195928034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115712 104203511 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115840 91724523 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 115968 174406850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 115968 86002570 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116096 88404280 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 116224 388119795 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 116224 183840477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116224 92934000 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116352 90906477 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 116480 204279318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116480 98924107 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116608 105355211 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 116736 1603336751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 116736 787846381 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 116736 432852239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 116736 238096322 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116736 117285587 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116864 120810735 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 116992 194755917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 116992 101056579 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 117120 93699338 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 117248 354994142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 117248 184288381 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 117248 91968127 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 117376 92320254 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 117504 170705761 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 117504 88051877 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 117632 82653884 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 117760 815490370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 117760 383654089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 117760 184366891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 117760 89641409 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 117888 94725482 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 118016 199287198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118016 96290129 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118144 102997069 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 118272 431836281 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 118272 212610950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118272 100889619 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118400 111721331 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 118528 219225331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118528 111940110 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118656 107285221 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 118784 2935534112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 118784 1945061358 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 118784 992657254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 118784 482279629 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 118784 239284423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118784 118924357 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 118912 120360066 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 119040 242995206 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119040 122296048 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119168 120699158 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 119296 510377625 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 119296 250486206 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119296 118507405 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119424 131978801 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 119552 259891419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119552 133679179 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119680 126212240 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 119808 952404104 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 119808 451137626 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 119808 229118474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119808 116901398 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 119936 112217076 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 120064 222019152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120064 109990899 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120192 112028253 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 120320 501266478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 120320 251630479 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120320 120681838 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120448 130948641 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 120576 249635999 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120576 130339864 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120704 119296135 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 120832 990472754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 120832 600397561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 120832 352007333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 120832 195189567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120832 110113991 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 120960 85075576 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 121088 156817766 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121088 75790087 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121216 81027679 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 121344 248390228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 121344 139246757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121344 72418127 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121472 66828630 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 121600 109143471 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121600 53730895 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121728 55412576 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 121856 390075193 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 121856 228274780 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 121856 130736659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121856 70054460 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 121984 60682199 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 122112 97538121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 122112 53981595 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 122240 43556526 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 122368 161800413 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 122368 80508631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 122368 39466792 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 122496 41041839 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 122624 81291782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 122624 38463733 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 122752 42828049 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 122880 1937755092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 122880 725651514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 122880 500233741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 122880 295834126 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 122880 173003556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 122880 84952992 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 122880 42067788 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123008 42885204 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 123136 88050564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123136 47183869 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123264 40866695 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 123392 122830570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 123392 71530047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123392 43992645 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123520 27537402 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 123648 51300523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123648 24184805 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123776 27115718 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 123904 204399615 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 123904 124681138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 123904 62738431 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 123904 27330206 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124032 35408225 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 124160 61942707 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124160 35258644 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124288 26684063 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 124416 79718477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 124416 42321764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124416 20662905 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124544 21658859 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 124672 37396713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124672 19482324 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124800 17914389 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 124928 225417773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 124928 106363350 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 124928 76689061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 124928 47696814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 124928 28354124 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125056 19342690 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 125184 28992247 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125184 14755362 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125312 14236885 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 125440 29674289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 125440 18391886 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125440 10820679 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125568 7571207 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 125696 11282403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125696 2981854 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125824 8300549 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 125952 119054423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 125952 47881338 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 125952 20078582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 125952 12807603 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126080 7270979 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 126208 27802756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126208 11774692 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126336 16028064 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 126464 71173085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 126464 28685632 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126464 10527132 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126592 18158500 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 126720 42487453 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126720 17880170 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126848 24607283 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 126976 1212103578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 126976 964593539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 126976 472068751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 126976 196081945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 126976 84364774 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 126976 37128076 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 127104 47236698 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 127232 111717171 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 127232 50842114 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 127360 60875057 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 127488 275986806 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 127488 139110155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 127488 67266413 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 127616 71843742 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 127744 136876651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 127744 72836071 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 127872 64040580 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 128000 492524788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 128000 263863595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 128000 139763759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128000 66412116 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128128 73351643 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 128256 124099836 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128256 64074387 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128384 60025449 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 128512 228661193 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 128512 112004368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128512 56993997 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128640 55010371 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 128768 116656825 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128768 60583153 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128896 56073672 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 129024 247510039 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 129024 133449269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 129024 109475563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 129024 67145387 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129024 38827980 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129152 28317407 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 129280 42330176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129280 26409915 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129408 15920261 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 129536 23973706 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 129536 11495633 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129536 2708434 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129664 8787199 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 129792 12478073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129792 6984667 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 129920 5493406 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 130048 114060770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 130048 42502730 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 130048 13861642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130048 10536663 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130176 3324979 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 130304 28641088 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130304 6181447 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130432 22459641 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 130560 71558040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 130560 45117814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130560 24023202 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130688 21094612 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 130816 26440226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130816 14067447 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 130944 12372779 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 114688 (MobiusHarmonicTree.branch 8059878917 mobiusHarmonicBlock014 mobiusHarmonicBlock015) = true := Helfgott.combined

#print axioms solution
