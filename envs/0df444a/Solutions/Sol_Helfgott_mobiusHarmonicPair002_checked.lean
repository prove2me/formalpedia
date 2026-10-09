-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair002_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:53:18.230026+00:00
-- url     : https://prove2.me/submissions/8237f15d-616b-4a33-ae0a-ef7a2536cb86

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32768 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32832 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 84490150 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32896 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32960 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 74986267 d11 d12
private def d6 : MobiusHarmonicTree := .branch 159476417 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33024 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33088 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 25061329 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33152 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33216 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 16099317 d18 d19
private def d13 : MobiusHarmonicTree := .branch 41160646 d14 d17
private def d5 : MobiusHarmonicTree := .branch 200637063 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33280 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33344 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 20382230 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33408 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33472 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 10962319 d26 d27
private def d21 : MobiusHarmonicTree := .branch 31344549 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33536 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33600 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 54969860 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33664 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33728 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 75626828 d33 d34
private def d28 : MobiusHarmonicTree := .branch 130596688 d29 d32
private def d20 : MobiusHarmonicTree := .branch 161941237 d21 d28
private def d4 : MobiusHarmonicTree := .branch 362578300 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33792 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33856 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 85243567 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33920 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 33984 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 94113237 d42 d43
private def d37 : MobiusHarmonicTree := .branch 179356804 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34048 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34112 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 84829109 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34176 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34240 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 94343503 d49 d50
private def d44 : MobiusHarmonicTree := .branch 179172612 d45 d48
private def d36 : MobiusHarmonicTree := .branch 358529416 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34304 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34368 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 88816428 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34432 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34496 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 100168140 d57 d58
private def d52 : MobiusHarmonicTree := .branch 188984568 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34560 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34624 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 115073301 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34688 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34752 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 129119849 d64 d65
private def d59 : MobiusHarmonicTree := .branch 244193150 d60 d63
private def d51 : MobiusHarmonicTree := .branch 433177718 d52 d59
private def d35 : MobiusHarmonicTree := .branch 791707134 d36 d51
private def d3 : MobiusHarmonicTree := .branch 1154285434 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34816 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34880 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 90375318 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 34944 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35008 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 55603586 d74 d75
private def d69 : MobiusHarmonicTree := .branch 145978904 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35072 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35136 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 57282628 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35200 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35264 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 68394582 d81 d82
private def d76 : MobiusHarmonicTree := .branch 125677210 d77 d80
private def d68 : MobiusHarmonicTree := .branch 271656114 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35328 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35392 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 93326324 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35456 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35520 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 80069293 d89 d90
private def d84 : MobiusHarmonicTree := .branch 173395617 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35584 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35648 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 79093245 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35712 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35776 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 59152571 d96 d97
private def d91 : MobiusHarmonicTree := .branch 138245816 d92 d95
private def d83 : MobiusHarmonicTree := .branch 311641433 d84 d91
private def d67 : MobiusHarmonicTree := .branch 583297547 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35840 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35904 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 28194802 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 35968 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36032 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 33124702 d105 d106
private def d100 : MobiusHarmonicTree := .branch 61319504 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36096 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36160 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 19113947 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36224 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36288 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 18910722 d112 d113
private def d107 : MobiusHarmonicTree := .branch 38024669 d108 d111
private def d99 : MobiusHarmonicTree := .branch 99344173 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36352 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36416 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 10350112 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36480 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36544 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 18739658 d120 d121
private def d115 : MobiusHarmonicTree := .branch 29089770 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36608 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36672 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 19988324 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36736 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36800 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 17174223 d127 d128
private def d122 : MobiusHarmonicTree := .branch 37162547 d123 d126
private def d114 : MobiusHarmonicTree := .branch 66252317 d115 d122
private def d98 : MobiusHarmonicTree := .branch 165596490 d99 d114
private def d66 : MobiusHarmonicTree := .branch 748894037 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1903179471 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36864 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36928 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 52684328 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 36992 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37056 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 52519513 d138 d139
private def d133 : MobiusHarmonicTree := .branch 105203841 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37120 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37184 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 39902470 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37248 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37312 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 89742589 d145 d146
private def d140 : MobiusHarmonicTree := .branch 129645059 d141 d144
private def d132 : MobiusHarmonicTree := .branch 234848900 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37376 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37440 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 100517671 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37504 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37568 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 116499091 d153 d154
private def d148 : MobiusHarmonicTree := .branch 217016762 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37632 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37696 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 135531096 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37760 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37824 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 116543487 d160 d161
private def d155 : MobiusHarmonicTree := .branch 252074583 d156 d159
private def d147 : MobiusHarmonicTree := .branch 469091345 d148 d155
private def d131 : MobiusHarmonicTree := .branch 703940245 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37888 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 37952 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 102185930 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38016 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38080 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 96595921 d169 d170
private def d164 : MobiusHarmonicTree := .branch 198781851 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38144 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38208 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 92507012 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38272 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38336 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 115236587 d176 d177
private def d171 : MobiusHarmonicTree := .branch 207743599 d172 d175
private def d163 : MobiusHarmonicTree := .branch 406525450 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38400 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38464 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 81726082 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38528 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38592 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 56539042 d184 d185
private def d179 : MobiusHarmonicTree := .branch 138265124 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38656 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38720 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 65747437 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38784 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38848 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 62424165 d191 d192
private def d186 : MobiusHarmonicTree := .branch 128171602 d187 d190
private def d178 : MobiusHarmonicTree := .branch 266436726 d179 d186
private def d162 : MobiusHarmonicTree := .branch 672962176 d163 d178
private def d130 : MobiusHarmonicTree := .branch 1376902421 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38912 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 38976 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 34166603 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39040 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39104 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 8128593 d201 d202
private def d196 : MobiusHarmonicTree := .branch 42295196 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39168 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39232 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 38018103 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39296 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39360 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 73525052 d208 d209
private def d203 : MobiusHarmonicTree := .branch 111543155 d204 d207
private def d195 : MobiusHarmonicTree := .branch 153838351 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39424 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39488 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 73216433 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39552 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39616 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 53945443 d216 d217
private def d211 : MobiusHarmonicTree := .branch 127161876 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39680 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39744 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 29930310 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39808 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39872 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 21358702 d223 d224
private def d218 : MobiusHarmonicTree := .branch 51289012 d219 d222
private def d210 : MobiusHarmonicTree := .branch 178450888 d211 d218
private def d194 : MobiusHarmonicTree := .branch 332289239 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 39936 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40000 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 27153126 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40064 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40128 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 29042978 d232 d233
private def d227 : MobiusHarmonicTree := .branch 56196104 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40192 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40256 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 44890198 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40320 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40384 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 32887886 d239 d240
private def d234 : MobiusHarmonicTree := .branch 77778084 d235 d238
private def d226 : MobiusHarmonicTree := .branch 133974188 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40448 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40512 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 12884151 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40576 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40640 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 9107551 d247 d248
private def d242 : MobiusHarmonicTree := .branch 21991702 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40704 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40768 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 6034527 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40832 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock004 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40896 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 17360691 d254 d255
private def d249 : MobiusHarmonicTree := .branch 23395218 d250 d253
private def d241 : MobiusHarmonicTree := .branch 45386920 d242 d249
private def d225 : MobiusHarmonicTree := .branch 179361108 d226 d241
private def d193 : MobiusHarmonicTree := .branch 511650347 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1888552768 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3791732239 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 40960 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41024 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 24991065 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41088 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41152 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 8408152 d266 d267
private def d261 : MobiusHarmonicTree := .branch 33399217 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41216 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41280 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 33857365 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41344 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41408 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 33475230 d273 d274
private def d268 : MobiusHarmonicTree := .branch 67332595 d269 d272
private def d260 : MobiusHarmonicTree := .branch 100731812 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41472 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41536 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 32446867 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41600 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41664 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 59639994 d281 d282
private def d276 : MobiusHarmonicTree := .branch 92086861 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41728 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41792 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 69413699 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41856 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41920 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 86442765 d288 d289
private def d283 : MobiusHarmonicTree := .branch 155856464 d284 d287
private def d275 : MobiusHarmonicTree := .branch 247943325 d276 d283
private def d259 : MobiusHarmonicTree := .branch 348675137 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 41984 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42048 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 120787583 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42112 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42176 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 138727954 d297 d298
private def d292 : MobiusHarmonicTree := .branch 259515537 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42240 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42304 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 146313727 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42368 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42432 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 174014843 d304 d305
private def d299 : MobiusHarmonicTree := .branch 320328570 d300 d303
private def d291 : MobiusHarmonicTree := .branch 579844107 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42496 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42560 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 205120316 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42624 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42688 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 203707264 d312 d313
private def d307 : MobiusHarmonicTree := .branch 408827580 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42752 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42816 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 235166151 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42880 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 42944 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 245949322 d319 d320
private def d314 : MobiusHarmonicTree := .branch 481115473 d315 d318
private def d306 : MobiusHarmonicTree := .branch 889943053 d307 d314
private def d290 : MobiusHarmonicTree := .branch 1469787160 d291 d306
private def d258 : MobiusHarmonicTree := .branch 1818462297 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43008 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43072 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 208752597 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43136 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43200 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 169837269 d329 d330
private def d324 : MobiusHarmonicTree := .branch 378589866 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43264 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43328 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 138119384 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43392 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43456 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 109981287 d336 d337
private def d331 : MobiusHarmonicTree := .branch 248100671 d332 d335
private def d323 : MobiusHarmonicTree := .branch 626690537 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43520 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43584 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 100540570 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43648 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43712 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 69003997 d344 d345
private def d339 : MobiusHarmonicTree := .branch 169544567 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43776 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43840 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 65771719 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43904 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 43968 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 47689229 d351 d352
private def d346 : MobiusHarmonicTree := .branch 113460948 d347 d350
private def d338 : MobiusHarmonicTree := .branch 283005515 d339 d346
private def d322 : MobiusHarmonicTree := .branch 909696052 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44032 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44096 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 63480028 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44160 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44224 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 31480688 d360 d361
private def d355 : MobiusHarmonicTree := .branch 94960716 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44288 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44352 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 8977890 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44416 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44480 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 12877484 d367 d368
private def d362 : MobiusHarmonicTree := .branch 21855374 d363 d366
private def d354 : MobiusHarmonicTree := .branch 116816090 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44544 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44608 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 14598050 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44672 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44736 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 7105955 d375 d376
private def d370 : MobiusHarmonicTree := .branch 21704005 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44800 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44864 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 12438946 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44928 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 44992 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 3911095 d382 d383
private def d377 : MobiusHarmonicTree := .branch 16350041 d378 d381
private def d369 : MobiusHarmonicTree := .branch 38054046 d370 d377
private def d353 : MobiusHarmonicTree := .branch 154870136 d354 d369
private def d321 : MobiusHarmonicTree := .branch 1064566188 d322 d353
private def d257 : MobiusHarmonicTree := .branch 2883028485 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45056 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45120 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 11320916 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45184 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45248 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 12382045 d393 d394
private def d388 : MobiusHarmonicTree := .branch 23702961 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45312 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45376 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 2799162 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45440 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45504 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 6066333 d400 d401
private def d395 : MobiusHarmonicTree := .branch 8865495 d396 d399
private def d387 : MobiusHarmonicTree := .branch 32568456 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45568 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45632 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 4536440 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45696 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45760 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 20972950 d408 d409
private def d403 : MobiusHarmonicTree := .branch 25509390 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45824 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45888 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 42226981 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 45952 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46016 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 73489148 d415 d416
private def d410 : MobiusHarmonicTree := .branch 115716129 d411 d414
private def d402 : MobiusHarmonicTree := .branch 141225519 d403 d410
private def d386 : MobiusHarmonicTree := .branch 173793975 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46080 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46144 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 98863538 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46208 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46272 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 95416513 d424 d425
private def d419 : MobiusHarmonicTree := .branch 194280051 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46336 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46400 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 117451493 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46464 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46528 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 93350368 d431 d432
private def d426 : MobiusHarmonicTree := .branch 210801861 d427 d430
private def d418 : MobiusHarmonicTree := .branch 405081912 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46592 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46656 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 102026213 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46720 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46784 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 94268859 d439 d440
private def d434 : MobiusHarmonicTree := .branch 196295072 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46848 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46912 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 101955412 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 46976 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47040 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 128377264 d446 d447
private def d441 : MobiusHarmonicTree := .branch 230332676 d442 d445
private def d433 : MobiusHarmonicTree := .branch 426627748 d434 d441
private def d417 : MobiusHarmonicTree := .branch 831709660 d418 d433
private def d385 : MobiusHarmonicTree := .branch 1005503635 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47104 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47168 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 135870321 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47232 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47296 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 168434424 d456 d457
private def d451 : MobiusHarmonicTree := .branch 304304745 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47360 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47424 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 164456023 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47488 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47552 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 166181889 d463 d464
private def d458 : MobiusHarmonicTree := .branch 330637912 d459 d462
private def d450 : MobiusHarmonicTree := .branch 634942657 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47616 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47680 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 153106611 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47744 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47808 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 158868413 d471 d472
private def d466 : MobiusHarmonicTree := .branch 311975024 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47872 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 47936 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 152098047 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48000 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48064 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 178010741 d478 d479
private def d473 : MobiusHarmonicTree := .branch 330108788 d474 d477
private def d465 : MobiusHarmonicTree := .branch 642083812 d466 d473
private def d449 : MobiusHarmonicTree := .branch 1277026469 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48128 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48192 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 207142379 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48256 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48320 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 221398251 d487 d488
private def d482 : MobiusHarmonicTree := .branch 428540630 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48384 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48448 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 242196526 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48512 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48576 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 220940391 d494 d495
private def d489 : MobiusHarmonicTree := .branch 463136917 d490 d493
private def d481 : MobiusHarmonicTree := .branch 891677547 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48640 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48704 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 212530137 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48768 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48832 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 197314699 d502 d503
private def d497 : MobiusHarmonicTree := .branch 409844836 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48896 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 48960 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 199898140 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49024 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock005 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49088 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 192876534 d509 d510
private def d504 : MobiusHarmonicTree := .branch 392774674 d505 d508
private def d496 : MobiusHarmonicTree := .branch 802619510 d497 d504
private def d480 : MobiusHarmonicTree := .branch 1694297057 d481 d496
private def d448 : MobiusHarmonicTree := .branch 2971323526 d449 d480
private def d384 : MobiusHarmonicTree := .branch 3976827161 d385 d448
private def d256 : MobiusHarmonicTree := .branch 6859855646 d257 d384
private def d0 : MobiusHarmonicTree := .branch 10651587885 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 32768 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 32768 10651587885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 32768 3791732239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 32768 1903179471 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 32768 1154285434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 32768 362578300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 32768 200637063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 32768 159476417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32768 84490150 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32896 74986267 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 33024 41160646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33024 25061329 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33152 16099317 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 33280 161941237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 33280 31344549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33280 20382230 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33408 10962319 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 33536 130596688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33536 54969860 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33664 75626828 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 33792 791707134 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 33792 358529416 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 33792 179356804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33792 85243567 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 33920 94113237 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 34048 179172612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34048 84829109 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34176 94343503 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 34304 433177718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 34304 188984568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34304 88816428 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34432 100168140 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 34560 244193150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34560 115073301 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34688 129119849 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 34816 748894037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 34816 583297547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 34816 271656114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 34816 145978904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34816 90375318 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 34944 55603586 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 35072 125677210 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35072 57282628 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35200 68394582 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 35328 311641433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 35328 173395617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35328 93326324 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35456 80069293 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 35584 138245816 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35584 79093245 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35712 59152571 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 35840 165596490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 35840 99344173 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 35840 61319504 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35840 28194802 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 35968 33124702 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 36096 38024669 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36096 19113947 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36224 18910722 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 36352 66252317 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 36352 29089770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36352 10350112 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36480 18739658 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 36608 37162547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36608 19988324 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36736 17174223 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 36864 1888552768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 36864 1376902421 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 36864 703940245 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 36864 234848900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 36864 105203841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36864 52684328 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 36992 52519513 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 37120 129645059 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 37120 39902470 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 37248 89742589 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 37376 469091345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 37376 217016762 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 37376 100517671 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 37504 116499091 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 37632 252074583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 37632 135531096 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 37760 116543487 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 37888 672962176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 37888 406525450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 37888 198781851 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 37888 102185930 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38016 96595921 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 38144 207743599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38144 92507012 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38272 115236587 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 38400 266436726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 38400 138265124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38400 81726082 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38528 56539042 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 38656 128171602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38656 65747437 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38784 62424165 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 38912 511650347 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 38912 332289239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 38912 153838351 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 38912 42295196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 38912 34166603 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39040 8128593 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 39168 111543155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39168 38018103 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39296 73525052 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 39424 178450888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 39424 127161876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39424 73216433 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39552 53945443 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 39680 51289012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39680 29930310 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39808 21358702 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 39936 179361108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 39936 133974188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 39936 56196104 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 39936 27153126 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40064 29042978 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 40192 77778084 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40192 44890198 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40320 32887886 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 40448 45386920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 40448 21991702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40448 12884151 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40576 9107551 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 40704 23395218 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40704 6034527 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40832 17360691 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 40960 6859855646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 40960 2883028485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 40960 1818462297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 40960 348675137 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 40960 100731812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 40960 33399217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 40960 24991065 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41088 8408152 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 41216 67332595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41216 33857365 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41344 33475230 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 41472 247943325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 41472 92086861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41472 32446867 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41600 59639994 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 41728 155856464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41728 69413699 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41856 86442765 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 41984 1469787160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 41984 579844107 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 41984 259515537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 41984 120787583 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 42112 138727954 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 42240 320328570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 42240 146313727 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 42368 174014843 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 42496 889943053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 42496 408827580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 42496 205120316 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 42624 203707264 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 42752 481115473 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 42752 235166151 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 42880 245949322 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 43008 1064566188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 43008 909696052 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 43008 626690537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 43008 378589866 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43008 208752597 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43136 169837269 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 43264 248100671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43264 138119384 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43392 109981287 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 43520 283005515 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 43520 169544567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43520 100540570 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43648 69003997 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 43776 113460948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43776 65771719 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 43904 47689229 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 44032 154870136 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 44032 116816090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 44032 94960716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44032 63480028 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44160 31480688 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 44288 21855374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44288 8977890 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44416 12877484 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 44544 38054046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 44544 21704005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44544 14598050 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44672 7105955 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 44800 16350041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44800 12438946 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 44928 3911095 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 45056 3976827161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 45056 1005503635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 45056 173793975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 45056 32568456 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 45056 23702961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45056 11320916 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45184 12382045 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 45312 8865495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45312 2799162 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45440 6066333 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 45568 141225519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 45568 25509390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45568 4536440 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45696 20972950 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 45824 115716129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45824 42226981 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 45952 73489148 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 46080 831709660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 46080 405081912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 46080 194280051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46080 98863538 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46208 95416513 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 46336 210801861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46336 117451493 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46464 93350368 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 46592 426627748 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 46592 196295072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46592 102026213 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46720 94268859 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 46848 230332676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46848 101955412 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 46976 128377264 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 47104 2971323526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 47104 1277026469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 47104 634942657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 47104 304304745 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 47104 135870321 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 47232 168434424 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 47360 330637912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 47360 164456023 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 47488 166181889 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 47616 642083812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 47616 311975024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 47616 153106611 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 47744 158868413 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 47872 330108788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 47872 152098047 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48000 178010741 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 48128 1694297057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 48128 891677547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 48128 428540630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48128 207142379 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48256 221398251 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 48384 463136917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48384 242196526 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48512 220940391 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 48640 802619510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 48640 409844836 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48640 212530137 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48768 197314699 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 48896 392774674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 48896 199898140 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49024 192876534 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 32768 (MobiusHarmonicTree.branch 10651587885 mobiusHarmonicBlock004 mobiusHarmonicBlock005) = true := Helfgott.combined

#print axioms solution
