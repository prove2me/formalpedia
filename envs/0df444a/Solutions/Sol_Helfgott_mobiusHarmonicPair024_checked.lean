-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair024_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:20:53.779246+00:00
-- url     : https://prove2.me/submissions/dd0d3cb6-670e-4850-837e-481014c6869a

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393216 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393280 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 801058 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393344 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393408 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 907483 d11 d12
private def d6 : MobiusHarmonicTree := .branch 1708541 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393472 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393536 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 2601923 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393600 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393664 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 8220223 d18 d19
private def d13 : MobiusHarmonicTree := .branch 10822146 d14 d17
private def d5 : MobiusHarmonicTree := .branch 12530687 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393728 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393792 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 8603744 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393856 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393920 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 10395457 d26 d27
private def d21 : MobiusHarmonicTree := .branch 18999201 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393984 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394048 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 14066802 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394112 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394176 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 13476357 d33 d34
private def d28 : MobiusHarmonicTree := .branch 27543159 d29 d32
private def d20 : MobiusHarmonicTree := .branch 46542360 d21 d28
private def d4 : MobiusHarmonicTree := .branch 59073047 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394240 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394304 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 13492265 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394368 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394432 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 12032682 d42 d43
private def d37 : MobiusHarmonicTree := .branch 25524947 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394496 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394560 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 8280242 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394624 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394688 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 9290915 d49 d50
private def d44 : MobiusHarmonicTree := .branch 17571157 d45 d48
private def d36 : MobiusHarmonicTree := .branch 43096104 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394752 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394816 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 10957057 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394880 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 394944 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 9644522 d57 d58
private def d52 : MobiusHarmonicTree := .branch 20601579 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395008 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395072 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 12827973 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395136 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395200 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 15020382 d64 d65
private def d59 : MobiusHarmonicTree := .branch 27848355 d60 d63
private def d51 : MobiusHarmonicTree := .branch 48449934 d52 d59
private def d35 : MobiusHarmonicTree := .branch 91546038 d36 d51
private def d3 : MobiusHarmonicTree := .branch 150619085 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395264 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395328 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 14668969 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395392 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395456 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 12433780 d74 d75
private def d69 : MobiusHarmonicTree := .branch 27102749 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395520 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395584 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 13400451 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395648 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395712 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 13315388 d81 d82
private def d76 : MobiusHarmonicTree := .branch 26715839 d77 d80
private def d68 : MobiusHarmonicTree := .branch 53818588 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395776 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395840 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 7518405 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395904 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 395968 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 6422381 d89 d90
private def d84 : MobiusHarmonicTree := .branch 13940786 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396032 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396096 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 6627265 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396160 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396224 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 4550434 d96 d97
private def d91 : MobiusHarmonicTree := .branch 11177699 d92 d95
private def d83 : MobiusHarmonicTree := .branch 25118485 d84 d91
private def d67 : MobiusHarmonicTree := .branch 78937073 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396288 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396352 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 8060969 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396416 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396480 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 6040827 d105 d106
private def d100 : MobiusHarmonicTree := .branch 14101796 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396544 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396608 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 5773940 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396672 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396736 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 4917847 d112 d113
private def d107 : MobiusHarmonicTree := .branch 10691787 d108 d111
private def d99 : MobiusHarmonicTree := .branch 24793583 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396800 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396864 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 874397 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396928 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 396992 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 1919518 d120 d121
private def d115 : MobiusHarmonicTree := .branch 2793915 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397056 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397120 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 2261245 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397184 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397248 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 3864097 d127 d128
private def d122 : MobiusHarmonicTree := .branch 6125342 d123 d126
private def d114 : MobiusHarmonicTree := .branch 8919257 d115 d122
private def d98 : MobiusHarmonicTree := .branch 33712840 d99 d114
private def d66 : MobiusHarmonicTree := .branch 112649913 d67 d98
private def d2 : MobiusHarmonicTree := .branch 263268998 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397312 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397376 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 2964506 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397440 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397504 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 1549789 d138 d139
private def d133 : MobiusHarmonicTree := .branch 4514295 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397568 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397632 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 1285096 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397696 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397760 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 2715304 d145 d146
private def d140 : MobiusHarmonicTree := .branch 4000400 d141 d144
private def d132 : MobiusHarmonicTree := .branch 8514695 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397824 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397888 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 4948478 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 397952 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398016 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 9675641 d153 d154
private def d148 : MobiusHarmonicTree := .branch 14624119 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398080 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398144 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 8263532 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398208 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398272 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 5915599 d160 d161
private def d155 : MobiusHarmonicTree := .branch 14179131 d156 d159
private def d147 : MobiusHarmonicTree := .branch 28803250 d148 d155
private def d131 : MobiusHarmonicTree := .branch 37317945 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398336 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398400 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 7098479 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398464 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398528 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 5595643 d169 d170
private def d164 : MobiusHarmonicTree := .branch 12694122 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398592 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398656 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 5631590 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398720 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398784 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 4107555 d176 d177
private def d171 : MobiusHarmonicTree := .branch 9739145 d172 d175
private def d163 : MobiusHarmonicTree := .branch 22433267 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398848 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398912 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 5414757 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 398976 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399040 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 6934145 d184 d185
private def d179 : MobiusHarmonicTree := .branch 12348902 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399104 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399168 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6458586 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399232 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399296 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 5567322 d191 d192
private def d186 : MobiusHarmonicTree := .branch 12025908 d187 d190
private def d178 : MobiusHarmonicTree := .branch 24374810 d179 d186
private def d162 : MobiusHarmonicTree := .branch 46808077 d163 d178
private def d130 : MobiusHarmonicTree := .branch 84126022 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399360 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399424 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 8136646 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399488 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399552 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 9746101 d201 d202
private def d196 : MobiusHarmonicTree := .branch 17882747 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399616 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399680 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 8239156 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399744 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399808 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 8166447 d208 d209
private def d203 : MobiusHarmonicTree := .branch 16405603 d204 d207
private def d195 : MobiusHarmonicTree := .branch 34288350 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399872 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 399936 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 7136367 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400000 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400064 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 5471693 d216 d217
private def d211 : MobiusHarmonicTree := .branch 12608060 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400128 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400192 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 4295543 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400256 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400320 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 3337345 d223 d224
private def d218 : MobiusHarmonicTree := .branch 7632888 d219 d222
private def d210 : MobiusHarmonicTree := .branch 20240948 d211 d218
private def d194 : MobiusHarmonicTree := .branch 54529298 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400384 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400448 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 3468732 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400512 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400576 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 3692223 d232 d233
private def d227 : MobiusHarmonicTree := .branch 7160955 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400640 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400704 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 3144539 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400768 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400832 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 5521106 d239 d240
private def d234 : MobiusHarmonicTree := .branch 8665645 d235 d238
private def d226 : MobiusHarmonicTree := .branch 15826600 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400896 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 400960 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 9971008 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401024 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401088 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 10598806 d247 d248
private def d242 : MobiusHarmonicTree := .branch 20569814 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401152 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401216 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 11096408 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401280 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock048 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401344 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 8416755 d254 d255
private def d249 : MobiusHarmonicTree := .branch 19513163 d250 d253
private def d241 : MobiusHarmonicTree := .branch 40082977 d242 d249
private def d225 : MobiusHarmonicTree := .branch 55909577 d226 d241
private def d193 : MobiusHarmonicTree := .branch 110438875 d194 d225
private def d129 : MobiusHarmonicTree := .branch 194564897 d130 d193
private def d1 : MobiusHarmonicTree := .branch 457833895 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401408 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401472 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 10058053 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401536 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401600 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 7617123 d266 d267
private def d261 : MobiusHarmonicTree := .branch 17675176 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401664 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401728 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 5528673 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401792 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401856 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 6452649 d273 d274
private def d268 : MobiusHarmonicTree := .branch 11981322 d269 d272
private def d260 : MobiusHarmonicTree := .branch 29656498 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401920 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 401984 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 5982809 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402048 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402112 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 4750036 d281 d282
private def d276 : MobiusHarmonicTree := .branch 10732845 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402176 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402240 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 7488030 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402304 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402368 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 4965778 d288 d289
private def d283 : MobiusHarmonicTree := .branch 12453808 d284 d287
private def d275 : MobiusHarmonicTree := .branch 23186653 d276 d283
private def d259 : MobiusHarmonicTree := .branch 52843151 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402432 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402496 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 6342935 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402560 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402624 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 7205300 d297 d298
private def d292 : MobiusHarmonicTree := .branch 13548235 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402688 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402752 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 8337767 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402816 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402880 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 6773853 d304 d305
private def d299 : MobiusHarmonicTree := .branch 15111620 d300 d303
private def d291 : MobiusHarmonicTree := .branch 28659855 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 402944 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403008 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 9138645 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403072 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403136 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 10678872 d312 d313
private def d307 : MobiusHarmonicTree := .branch 19817517 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403200 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403264 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 10683037 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403328 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403392 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 8413713 d319 d320
private def d314 : MobiusHarmonicTree := .branch 19096750 d315 d318
private def d306 : MobiusHarmonicTree := .branch 38914267 d307 d314
private def d290 : MobiusHarmonicTree := .branch 67574122 d291 d306
private def d258 : MobiusHarmonicTree := .branch 120417273 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403456 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403520 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 10743017 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403584 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403648 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 12540548 d329 d330
private def d324 : MobiusHarmonicTree := .branch 23283565 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403712 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403776 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 14782940 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403840 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403904 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 14946656 d336 d337
private def d331 : MobiusHarmonicTree := .branch 29729596 d332 d335
private def d323 : MobiusHarmonicTree := .branch 53013161 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 403968 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404032 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 15137493 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404096 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404160 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 16872081 d344 d345
private def d339 : MobiusHarmonicTree := .branch 32009574 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404224 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404288 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 16174316 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404352 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404416 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 12633231 d351 d352
private def d346 : MobiusHarmonicTree := .branch 28807547 d347 d350
private def d338 : MobiusHarmonicTree := .branch 60817121 d339 d346
private def d322 : MobiusHarmonicTree := .branch 113830282 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404480 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404544 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 9460114 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404608 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404672 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 14895923 d360 d361
private def d355 : MobiusHarmonicTree := .branch 24356037 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404736 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404800 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 17635873 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404864 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404928 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 18210779 d367 d368
private def d362 : MobiusHarmonicTree := .branch 35846652 d363 d366
private def d354 : MobiusHarmonicTree := .branch 60202689 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 404992 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405056 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 18167938 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405120 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405184 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 20000924 d375 d376
private def d370 : MobiusHarmonicTree := .branch 38168862 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405248 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405312 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 17843147 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405376 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405440 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 19292669 d382 d383
private def d377 : MobiusHarmonicTree := .branch 37135816 d378 d381
private def d369 : MobiusHarmonicTree := .branch 75304678 d370 d377
private def d353 : MobiusHarmonicTree := .branch 135507367 d354 d369
private def d321 : MobiusHarmonicTree := .branch 249337649 d322 d353
private def d257 : MobiusHarmonicTree := .branch 369754922 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405504 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405568 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 21037175 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405632 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405696 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 19302897 d393 d394
private def d388 : MobiusHarmonicTree := .branch 40340072 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405760 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405824 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 17105962 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405888 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 405952 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 18856953 d400 d401
private def d395 : MobiusHarmonicTree := .branch 35962915 d396 d399
private def d387 : MobiusHarmonicTree := .branch 76302987 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406016 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406080 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 21118975 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406144 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406208 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 22971037 d408 d409
private def d403 : MobiusHarmonicTree := .branch 44090012 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406272 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406336 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 21890853 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406400 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406464 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 25079678 d415 d416
private def d410 : MobiusHarmonicTree := .branch 46970531 d411 d414
private def d402 : MobiusHarmonicTree := .branch 91060543 d403 d410
private def d386 : MobiusHarmonicTree := .branch 167363530 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406528 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406592 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 26070549 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406656 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406720 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 24417313 d424 d425
private def d419 : MobiusHarmonicTree := .branch 50487862 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406784 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406848 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 30343082 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406912 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 406976 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 30584273 d431 d432
private def d426 : MobiusHarmonicTree := .branch 60927355 d427 d430
private def d418 : MobiusHarmonicTree := .branch 111415217 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407040 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407104 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 29579765 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407168 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407232 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 30785961 d439 d440
private def d434 : MobiusHarmonicTree := .branch 60365726 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407296 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407360 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 29242144 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407424 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407488 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 28432888 d446 d447
private def d441 : MobiusHarmonicTree := .branch 57675032 d442 d445
private def d433 : MobiusHarmonicTree := .branch 118040758 d434 d441
private def d417 : MobiusHarmonicTree := .branch 229455975 d418 d433
private def d385 : MobiusHarmonicTree := .branch 396819505 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407552 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407616 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 30766751 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407680 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407744 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 28861424 d456 d457
private def d451 : MobiusHarmonicTree := .branch 59628175 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407808 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407872 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 27133703 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 407936 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408000 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 24862860 d463 d464
private def d458 : MobiusHarmonicTree := .branch 51996563 d459 d462
private def d450 : MobiusHarmonicTree := .branch 111624738 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408064 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408128 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 25680693 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408192 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408256 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 26811607 d471 d472
private def d466 : MobiusHarmonicTree := .branch 52492300 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408320 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408384 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 29107516 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408448 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408512 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 28584276 d478 d479
private def d473 : MobiusHarmonicTree := .branch 57691792 d474 d477
private def d465 : MobiusHarmonicTree := .branch 110184092 d466 d473
private def d449 : MobiusHarmonicTree := .branch 221808830 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408576 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408640 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 27929437 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408704 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408768 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 26379263 d487 d488
private def d482 : MobiusHarmonicTree := .branch 54308700 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408832 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408896 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 27329852 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 408960 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409024 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 25504677 d494 d495
private def d489 : MobiusHarmonicTree := .branch 52834529 d490 d493
private def d481 : MobiusHarmonicTree := .branch 107143229 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409088 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409152 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 28344018 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409216 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409280 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 29383553 d502 d503
private def d497 : MobiusHarmonicTree := .branch 57727571 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409344 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409408 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 27146668 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409472 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock049 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 409536 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 24659715 d509 d510
private def d504 : MobiusHarmonicTree := .branch 51806383 d505 d508
private def d496 : MobiusHarmonicTree := .branch 109533954 d497 d504
private def d480 : MobiusHarmonicTree := .branch 216677183 d481 d496
private def d448 : MobiusHarmonicTree := .branch 438486013 d449 d480
private def d384 : MobiusHarmonicTree := .branch 835305518 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1205060440 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1662894335 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 393216 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 393216 1662894335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 393216 457833895 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 393216 263268998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 393216 150619085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 393216 59073047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 393216 12530687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 393216 1708541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393216 801058 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393344 907483 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 393472 10822146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393472 2601923 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393600 8220223 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 393728 46542360 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 393728 18999201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393728 8603744 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393856 10395457 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 393984 27543159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393984 14066802 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 394112 13476357 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 394240 91546038 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 394240 43096104 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 394240 25524947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 394240 13492265 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 394368 12032682 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 394496 17571157 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 394496 8280242 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 394624 9290915 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 394752 48449934 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 394752 20601579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 394752 10957057 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 394880 9644522 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 395008 27848355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395008 12827973 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395136 15020382 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 395264 112649913 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 395264 78937073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 395264 53818588 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 395264 27102749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395264 14668969 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395392 12433780 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 395520 26715839 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395520 13400451 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395648 13315388 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 395776 25118485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 395776 13940786 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395776 7518405 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 395904 6422381 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 396032 11177699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396032 6627265 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396160 4550434 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 396288 33712840 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 396288 24793583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 396288 14101796 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396288 8060969 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396416 6040827 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 396544 10691787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396544 5773940 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396672 4917847 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 396800 8919257 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 396800 2793915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396800 874397 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 396928 1919518 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 397056 6125342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397056 2261245 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397184 3864097 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 397312 194564897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 397312 84126022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 397312 37317945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 397312 8514695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 397312 4514295 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397312 2964506 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397440 1549789 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 397568 4000400 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397568 1285096 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397696 2715304 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 397824 28803250 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 397824 14624119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397824 4948478 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 397952 9675641 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 398080 14179131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398080 8263532 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398208 5915599 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 398336 46808077 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 398336 22433267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 398336 12694122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398336 7098479 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398464 5595643 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 398592 9739145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398592 5631590 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398720 4107555 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 398848 24374810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 398848 12348902 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398848 5414757 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 398976 6934145 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 399104 12025908 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 399104 6458586 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 399232 5567322 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 399360 110438875 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 399360 54529298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 399360 34288350 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 399360 17882747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 399360 8136646 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 399488 9746101 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 399616 16405603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 399616 8239156 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 399744 8166447 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 399872 20240948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 399872 12608060 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 399872 7136367 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400000 5471693 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 400128 7632888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400128 4295543 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400256 3337345 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 400384 55909577 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 400384 15826600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 400384 7160955 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400384 3468732 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400512 3692223 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 400640 8665645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400640 3144539 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400768 5521106 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 400896 40082977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 400896 20569814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 400896 9971008 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401024 10598806 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 401152 19513163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401152 11096408 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401280 8416755 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 401408 1205060440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 401408 369754922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 401408 120417273 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 401408 52843151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 401408 29656498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 401408 17675176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401408 10058053 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401536 7617123 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 401664 11981322 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401664 5528673 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401792 6452649 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 401920 23186653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 401920 10732845 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 401920 5982809 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402048 4750036 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 402176 12453808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402176 7488030 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402304 4965778 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 402432 67574122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 402432 28659855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 402432 13548235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402432 6342935 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402560 7205300 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 402688 15111620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402688 8337767 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402816 6773853 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 402944 38914267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 402944 19817517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 402944 9138645 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403072 10678872 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 403200 19096750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403200 10683037 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403328 8413713 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 403456 249337649 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 403456 113830282 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 403456 53013161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 403456 23283565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403456 10743017 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403584 12540548 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 403712 29729596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403712 14782940 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403840 14946656 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 403968 60817121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 403968 32009574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 403968 15137493 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404096 16872081 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 404224 28807547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404224 16174316 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404352 12633231 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 404480 135507367 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 404480 60202689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 404480 24356037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404480 9460114 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404608 14895923 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 404736 35846652 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404736 17635873 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404864 18210779 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 404992 75304678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 404992 38168862 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 404992 18167938 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 405120 20000924 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 405248 37135816 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 405248 17843147 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 405376 19292669 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 405504 835305518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 405504 396819505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 405504 167363530 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 405504 76302987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 405504 40340072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 405504 21037175 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 405632 19302897 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 405760 35962915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 405760 17105962 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 405888 18856953 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 406016 91060543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 406016 44090012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406016 21118975 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406144 22971037 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 406272 46970531 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406272 21890853 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406400 25079678 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 406528 229455975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 406528 111415217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 406528 50487862 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406528 26070549 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406656 24417313 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 406784 60927355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406784 30343082 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 406912 30584273 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 407040 118040758 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 407040 60365726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407040 29579765 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407168 30785961 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 407296 57675032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407296 29242144 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407424 28432888 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 407552 438486013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 407552 221808830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 407552 111624738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 407552 59628175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407552 30766751 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407680 28861424 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 407808 51996563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407808 27133703 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 407936 24862860 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 408064 110184092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 408064 52492300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408064 25680693 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408192 26811607 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 408320 57691792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408320 29107516 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408448 28584276 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 408576 216677183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 408576 107143229 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 408576 54308700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408576 27929437 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408704 26379263 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 408832 52834529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408832 27329852 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 408960 25504677 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 409088 109533954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 409088 57727571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409088 28344018 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409216 29383553 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 409344 51806383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409344 27146668 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 409472 24659715 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 393216 (MobiusHarmonicTree.branch 1662894335 mobiusHarmonicBlock048 mobiusHarmonicBlock049) = true := Helfgott.combined

#print axioms solution
