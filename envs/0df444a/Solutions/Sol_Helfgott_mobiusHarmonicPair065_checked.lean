-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair065_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:57:42.701237+00:00
-- url     : https://prove2.me/submissions/006d2fc7-c218-42ca-964a-ae250108a8ec

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064960 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065024 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 46380267 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065088 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065152 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 46976470 d11 d12
private def d6 : MobiusHarmonicTree := .branch 93356737 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065216 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065280 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 47908603 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065344 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065408 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 49106141 d18 d19
private def d13 : MobiusHarmonicTree := .branch 97014744 d14 d17
private def d5 : MobiusHarmonicTree := .branch 190371481 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065472 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065536 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 50066916 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065600 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065664 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 49909809 d26 d27
private def d21 : MobiusHarmonicTree := .branch 99976725 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065728 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065792 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 50364513 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065856 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065920 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 49901570 d33 d34
private def d28 : MobiusHarmonicTree := .branch 100266083 d29 d32
private def d20 : MobiusHarmonicTree := .branch 200242808 d21 d28
private def d4 : MobiusHarmonicTree := .branch 390614289 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1065984 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066048 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 50661966 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066112 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066176 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 50840670 d42 d43
private def d37 : MobiusHarmonicTree := .branch 101502636 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066240 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066304 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 50487566 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066368 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066432 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 50073599 d49 d50
private def d44 : MobiusHarmonicTree := .branch 100561165 d45 d48
private def d36 : MobiusHarmonicTree := .branch 202063801 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066496 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066560 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 50407002 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066624 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066688 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 50733755 d57 d58
private def d52 : MobiusHarmonicTree := .branch 101140757 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066752 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066816 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 51180407 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066880 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1066944 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 50913722 d64 d65
private def d59 : MobiusHarmonicTree := .branch 102094129 d60 d63
private def d51 : MobiusHarmonicTree := .branch 203234886 d52 d59
private def d35 : MobiusHarmonicTree := .branch 405298687 d36 d51
private def d3 : MobiusHarmonicTree := .branch 795912976 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067008 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067072 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 49620933 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067136 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067200 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 49370400 d74 d75
private def d69 : MobiusHarmonicTree := .branch 98991333 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067264 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067328 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 48610283 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067392 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067456 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 47217019 d81 d82
private def d76 : MobiusHarmonicTree := .branch 95827302 d77 d80
private def d68 : MobiusHarmonicTree := .branch 194818635 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067520 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067584 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 47104577 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067648 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067712 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 46441460 d89 d90
private def d84 : MobiusHarmonicTree := .branch 93546037 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067776 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067840 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 46360966 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067904 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1067968 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 46234616 d96 d97
private def d91 : MobiusHarmonicTree := .branch 92595582 d92 d95
private def d83 : MobiusHarmonicTree := .branch 186141619 d84 d91
private def d67 : MobiusHarmonicTree := .branch 380960254 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068032 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068096 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 46003449 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068160 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068224 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 46477235 d105 d106
private def d100 : MobiusHarmonicTree := .branch 92480684 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068288 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068352 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 46585855 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068416 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068480 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 46864790 d112 d113
private def d107 : MobiusHarmonicTree := .branch 93450645 d108 d111
private def d99 : MobiusHarmonicTree := .branch 185931329 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068544 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068608 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 47011697 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068672 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068736 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 47111829 d120 d121
private def d115 : MobiusHarmonicTree := .branch 94123526 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068800 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068864 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 45914261 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068928 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1068992 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 45554214 d127 d128
private def d122 : MobiusHarmonicTree := .branch 91468475 d123 d126
private def d114 : MobiusHarmonicTree := .branch 185592001 d115 d122
private def d98 : MobiusHarmonicTree := .branch 371523330 d99 d114
private def d66 : MobiusHarmonicTree := .branch 752483584 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1548396560 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069056 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069120 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 44735950 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069184 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069248 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 43636378 d138 d139
private def d133 : MobiusHarmonicTree := .branch 88372328 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069312 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069376 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 44173495 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069440 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069504 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 44608622 d145 d146
private def d140 : MobiusHarmonicTree := .branch 88782117 d141 d144
private def d132 : MobiusHarmonicTree := .branch 177154445 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069568 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069632 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 42592303 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069696 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069760 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 43966946 d153 d154
private def d148 : MobiusHarmonicTree := .branch 86559249 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069824 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069888 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 44522498 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1069952 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070016 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 43010668 d160 d161
private def d155 : MobiusHarmonicTree := .branch 87533166 d156 d159
private def d147 : MobiusHarmonicTree := .branch 174092415 d148 d155
private def d131 : MobiusHarmonicTree := .branch 351246860 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070080 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070144 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 42464463 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070208 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070272 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 42081905 d169 d170
private def d164 : MobiusHarmonicTree := .branch 84546368 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070336 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070400 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 41781665 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070464 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070528 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 40708994 d176 d177
private def d171 : MobiusHarmonicTree := .branch 82490659 d172 d175
private def d163 : MobiusHarmonicTree := .branch 167037027 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070592 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070656 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 40553715 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070720 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070784 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 41389385 d184 d185
private def d179 : MobiusHarmonicTree := .branch 81943100 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070848 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070912 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 40389045 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1070976 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071040 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 40772592 d191 d192
private def d186 : MobiusHarmonicTree := .branch 81161637 d187 d190
private def d178 : MobiusHarmonicTree := .branch 163104737 d179 d186
private def d162 : MobiusHarmonicTree := .branch 330141764 d163 d178
private def d130 : MobiusHarmonicTree := .branch 681388624 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071104 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071168 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 41461376 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071232 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071296 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 40343745 d201 d202
private def d196 : MobiusHarmonicTree := .branch 81805121 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071360 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071424 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 39469054 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071488 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071552 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 40901508 d208 d209
private def d203 : MobiusHarmonicTree := .branch 80370562 d204 d207
private def d195 : MobiusHarmonicTree := .branch 162175683 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071616 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071680 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 40244383 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071744 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071808 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 39936343 d216 d217
private def d211 : MobiusHarmonicTree := .branch 80180726 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071872 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1071936 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 39822427 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072000 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072064 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 39517311 d223 d224
private def d218 : MobiusHarmonicTree := .branch 79339738 d219 d222
private def d210 : MobiusHarmonicTree := .branch 159520464 d211 d218
private def d194 : MobiusHarmonicTree := .branch 321696147 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072128 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072192 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 38869077 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072256 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072320 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 37995269 d232 d233
private def d227 : MobiusHarmonicTree := .branch 76864346 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072384 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072448 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 38040147 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072512 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072576 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 39643866 d239 d240
private def d234 : MobiusHarmonicTree := .branch 77684013 d235 d238
private def d226 : MobiusHarmonicTree := .branch 154548359 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072640 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072704 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 40363499 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072768 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072832 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 39571989 d247 d248
private def d242 : MobiusHarmonicTree := .branch 79935488 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072896 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1072960 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 39954039 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073024 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock130 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073088 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 40992992 d254 d255
private def d249 : MobiusHarmonicTree := .branch 80947031 d250 d253
private def d241 : MobiusHarmonicTree := .branch 160882519 d242 d249
private def d225 : MobiusHarmonicTree := .branch 315430878 d226 d241
private def d193 : MobiusHarmonicTree := .branch 637127025 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1318515649 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2866912209 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073152 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073216 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 41290939 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073280 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073344 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 41512393 d266 d267
private def d261 : MobiusHarmonicTree := .branch 82803332 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073408 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073472 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 42258288 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073536 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073600 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 42852170 d273 d274
private def d268 : MobiusHarmonicTree := .branch 85110458 d269 d272
private def d260 : MobiusHarmonicTree := .branch 167913790 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073664 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073728 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 43472912 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073792 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073856 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 43137154 d281 d282
private def d276 : MobiusHarmonicTree := .branch 86610066 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073920 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1073984 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 43964409 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074048 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074112 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 45034482 d288 d289
private def d283 : MobiusHarmonicTree := .branch 88998891 d284 d287
private def d275 : MobiusHarmonicTree := .branch 175608957 d276 d283
private def d259 : MobiusHarmonicTree := .branch 343522747 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074176 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074240 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 46339829 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074304 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074368 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 45964782 d297 d298
private def d292 : MobiusHarmonicTree := .branch 92304611 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074432 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074496 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 46051440 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074560 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074624 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 46075743 d304 d305
private def d299 : MobiusHarmonicTree := .branch 92127183 d300 d303
private def d291 : MobiusHarmonicTree := .branch 184431794 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074688 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074752 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 45067242 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074816 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074880 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 44643232 d312 d313
private def d307 : MobiusHarmonicTree := .branch 89710474 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1074944 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075008 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 42813739 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075072 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075136 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 40525213 d319 d320
private def d314 : MobiusHarmonicTree := .branch 83338952 d315 d318
private def d306 : MobiusHarmonicTree := .branch 173049426 d307 d314
private def d290 : MobiusHarmonicTree := .branch 357481220 d291 d306
private def d258 : MobiusHarmonicTree := .branch 701003967 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075200 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075264 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 39770786 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075328 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075392 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 39895307 d329 d330
private def d324 : MobiusHarmonicTree := .branch 79666093 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075456 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075520 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 38733909 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075584 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075648 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 38792522 d336 d337
private def d331 : MobiusHarmonicTree := .branch 77526431 d332 d335
private def d323 : MobiusHarmonicTree := .branch 157192524 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075712 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075776 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 37929908 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075840 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075904 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 38594593 d344 d345
private def d339 : MobiusHarmonicTree := .branch 76524501 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1075968 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076032 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 39110445 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076096 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076160 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 38377274 d351 d352
private def d346 : MobiusHarmonicTree := .branch 77487719 d347 d350
private def d338 : MobiusHarmonicTree := .branch 154012220 d339 d346
private def d322 : MobiusHarmonicTree := .branch 311204744 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076224 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076288 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 40100845 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076352 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076416 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 40427782 d360 d361
private def d355 : MobiusHarmonicTree := .branch 80528627 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076480 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076544 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 39510761 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076608 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076672 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 41109157 d367 d368
private def d362 : MobiusHarmonicTree := .branch 80619918 d363 d366
private def d354 : MobiusHarmonicTree := .branch 161148545 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076736 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076800 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 41102432 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076864 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076928 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 40415025 d375 d376
private def d370 : MobiusHarmonicTree := .branch 81517457 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1076992 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077056 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 42524320 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077120 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077184 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 43701998 d382 d383
private def d377 : MobiusHarmonicTree := .branch 86226318 d378 d381
private def d369 : MobiusHarmonicTree := .branch 167743775 d370 d377
private def d353 : MobiusHarmonicTree := .branch 328892320 d354 d369
private def d321 : MobiusHarmonicTree := .branch 640097064 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1341101031 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077248 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077312 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 43112943 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077376 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077440 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 42288289 d393 d394
private def d388 : MobiusHarmonicTree := .branch 85401232 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077504 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077568 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 42965354 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077632 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077696 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 43620918 d400 d401
private def d395 : MobiusHarmonicTree := .branch 86586272 d396 d399
private def d387 : MobiusHarmonicTree := .branch 171987504 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077760 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077824 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 41890975 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077888 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1077952 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 41763546 d408 d409
private def d403 : MobiusHarmonicTree := .branch 83654521 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078016 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078080 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 41293864 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078144 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078208 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 40470940 d415 d416
private def d410 : MobiusHarmonicTree := .branch 81764804 d411 d414
private def d402 : MobiusHarmonicTree := .branch 165419325 d403 d410
private def d386 : MobiusHarmonicTree := .branch 337406829 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078272 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078336 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 41044809 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078400 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078464 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 40109901 d424 d425
private def d419 : MobiusHarmonicTree := .branch 81154710 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078528 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078592 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 41090690 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078656 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078720 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 41261022 d431 d432
private def d426 : MobiusHarmonicTree := .branch 82351712 d427 d430
private def d418 : MobiusHarmonicTree := .branch 163506422 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078784 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock131 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1078848 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 22449605 d436 d437
private def d438 : MobiusHarmonicTree := .leaf 0 0
private theorem p438 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 2 1078912 d438 = true := by decide +kernel

private def d434 : MobiusHarmonicTree := .branch 22449605 d435 d438
private def d439 : MobiusHarmonicTree := .leaf 0 0
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 3 1079040 d439 = true := by decide +kernel

private def d433 : MobiusHarmonicTree := .branch 22449605 d434 d439
private def d417 : MobiusHarmonicTree := .branch 185956027 d418 d433
private def d385 : MobiusHarmonicTree := .branch 523362856 d386 d417
private def d440 : MobiusHarmonicTree := .leaf 0 0
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 6 1079296 d440 = true := by decide +kernel

private def d384 : MobiusHarmonicTree := .branch 523362856 d385 d440
private def d256 : MobiusHarmonicTree := .branch 1864463887 d257 d384
private def d0 : MobiusHarmonicTree := .branch 4731376096 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 1064960 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 1064960 4731376096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1064960 2866912209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1064960 1548396560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1064960 795912976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1064960 390614289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1064960 190371481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1064960 93356737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064960 46380267 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065088 46976470 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1065216 97014744 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065216 47908603 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065344 49106141 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1065472 200242808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1065472 99976725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065472 50066916 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065600 49909809 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1065728 100266083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065728 50364513 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065856 49901570 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1065984 405298687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1065984 202063801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1065984 101502636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1065984 50661966 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1066112 50840670 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1066240 100561165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1066240 50487566 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1066368 50073599 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1066496 203234886 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1066496 101140757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1066496 50407002 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1066624 50733755 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1066752 102094129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1066752 51180407 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1066880 50913722 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1067008 752483584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1067008 380960254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1067008 194818635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1067008 98991333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067008 49620933 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067136 49370400 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1067264 95827302 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067264 48610283 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067392 47217019 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1067520 186141619 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1067520 93546037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067520 47104577 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067648 46441460 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1067776 92595582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067776 46360966 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1067904 46234616 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1068032 371523330 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1068032 185931329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1068032 92480684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068032 46003449 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068160 46477235 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1068288 93450645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068288 46585855 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068416 46864790 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1068544 185592001 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1068544 94123526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068544 47011697 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068672 47111829 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1068800 91468475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068800 45914261 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1068928 45554214 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1069056 1318515649 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1069056 681388624 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1069056 351246860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1069056 177154445 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1069056 88372328 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069056 44735950 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069184 43636378 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1069312 88782117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069312 44173495 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069440 44608622 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1069568 174092415 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1069568 86559249 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069568 42592303 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069696 43966946 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1069824 87533166 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069824 44522498 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1069952 43010668 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1070080 330141764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1070080 167037027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1070080 84546368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070080 42464463 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070208 42081905 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1070336 82490659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070336 41781665 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070464 40708994 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1070592 163104737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1070592 81943100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070592 40553715 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070720 41389385 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1070848 81161637 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070848 40389045 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1070976 40772592 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1071104 637127025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1071104 321696147 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1071104 162175683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1071104 81805121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1071104 41461376 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1071232 40343745 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1071360 80370562 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1071360 39469054 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1071488 40901508 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1071616 159520464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1071616 80180726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1071616 40244383 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1071744 39936343 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1071872 79339738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1071872 39822427 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072000 39517311 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1072128 315430878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1072128 154548359 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1072128 76864346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072128 38869077 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072256 37995269 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1072384 77684013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072384 38040147 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072512 39643866 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1072640 160882519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1072640 79935488 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072640 40363499 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072768 39571989 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1072896 80947031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1072896 39954039 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073024 40992992 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1073152 1864463887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1073152 1341101031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1073152 701003967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1073152 343522747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1073152 167913790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1073152 82803332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073152 41290939 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073280 41512393 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1073408 85110458 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073408 42258288 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073536 42852170 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1073664 175608957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1073664 86610066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073664 43472912 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073792 43137154 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1073920 88998891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1073920 43964409 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074048 45034482 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1074176 357481220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1074176 184431794 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1074176 92304611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074176 46339829 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074304 45964782 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1074432 92127183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074432 46051440 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074560 46075743 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1074688 173049426 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1074688 89710474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074688 45067242 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074816 44643232 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1074944 83338952 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1074944 42813739 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075072 40525213 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1075200 640097064 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1075200 311204744 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1075200 157192524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1075200 79666093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075200 39770786 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075328 39895307 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1075456 77526431 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075456 38733909 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075584 38792522 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1075712 154012220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1075712 76524501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075712 37929908 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075840 38594593 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1075968 77487719 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1075968 39110445 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076096 38377274 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1076224 328892320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1076224 161148545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1076224 80528627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076224 40100845 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076352 40427782 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1076480 80619918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076480 39510761 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076608 41109157 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1076736 167743775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1076736 81517457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076736 41102432 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076864 40415025 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1076992 86226318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1076992 42524320 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1077120 43701998 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1077248 523362856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1077248 523362856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1077248 337406829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1077248 171987504 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1077248 85401232 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1077248 43112943 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1077376 42288289 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1077504 86586272 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1077504 42965354 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1077632 43620918 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1077760 165419325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1077760 83654521 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1077760 41890975 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1077888 41763546 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1078016 81764804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1078016 41293864 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1078144 40470940 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1078272 185956027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1078272 163506422 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1078272 81154710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1078272 41044809 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1078400 40109901 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1078528 82351712 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1078528 41090690 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1078656 41261022 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1078784 22449605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1078784 22449605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1078784 22449605 _ _ (by decide) p436 p437 (by decide +kernel)) p438 (by decide +kernel)) p439 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) p440 (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 1064960 (MobiusHarmonicTree.branch 4731376096 mobiusHarmonicBlock130 mobiusHarmonicBlock131) = true := Helfgott.combined

#print axioms solution
