-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair054_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:13:49.009975+00:00
-- url     : https://prove2.me/submissions/a2c15474-4aad-4fe3-bcb7-abbe2c46fd22

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884736 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884800 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 16441090 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884864 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884928 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 17068126 d11 d12
private def d6 : MobiusHarmonicTree := .branch 33509216 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884992 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885056 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 17516481 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885120 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885184 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 16975079 d18 d19
private def d13 : MobiusHarmonicTree := .branch 34491560 d14 d17
private def d5 : MobiusHarmonicTree := .branch 68000776 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885248 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885312 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 18444389 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885376 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885440 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 19051621 d26 d27
private def d21 : MobiusHarmonicTree := .branch 37496010 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885504 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885568 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 18802698 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885632 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885696 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 17613341 d33 d34
private def d28 : MobiusHarmonicTree := .branch 36416039 d29 d32
private def d20 : MobiusHarmonicTree := .branch 73912049 d21 d28
private def d4 : MobiusHarmonicTree := .branch 141912825 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885760 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885824 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 18106374 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885888 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 885952 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 20036117 d42 d43
private def d37 : MobiusHarmonicTree := .branch 38142491 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886016 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886080 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 20639315 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886144 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886208 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 20502026 d49 d50
private def d44 : MobiusHarmonicTree := .branch 41141341 d45 d48
private def d36 : MobiusHarmonicTree := .branch 79283832 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886272 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886336 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 20435878 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886400 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886464 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 21333148 d57 d58
private def d52 : MobiusHarmonicTree := .branch 41769026 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886528 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886592 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 21356006 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886656 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886720 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 21885233 d64 d65
private def d59 : MobiusHarmonicTree := .branch 43241239 d60 d63
private def d51 : MobiusHarmonicTree := .branch 85010265 d52 d59
private def d35 : MobiusHarmonicTree := .branch 164294097 d36 d51
private def d3 : MobiusHarmonicTree := .branch 306206922 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886784 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886848 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 21354358 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886912 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 886976 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 21808989 d74 d75
private def d69 : MobiusHarmonicTree := .branch 43163347 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887040 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887104 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 20605377 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887168 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887232 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 19300539 d81 d82
private def d76 : MobiusHarmonicTree := .branch 39905916 d77 d80
private def d68 : MobiusHarmonicTree := .branch 83069263 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887296 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887360 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 18863904 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887424 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887488 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 18803715 d89 d90
private def d84 : MobiusHarmonicTree := .branch 37667619 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887552 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887616 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 18485544 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887680 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887744 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 18710417 d96 d97
private def d91 : MobiusHarmonicTree := .branch 37195961 d92 d95
private def d83 : MobiusHarmonicTree := .branch 74863580 d84 d91
private def d67 : MobiusHarmonicTree := .branch 157932843 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887808 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887872 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 18775299 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 887936 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888000 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 19181413 d105 d106
private def d100 : MobiusHarmonicTree := .branch 37956712 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888064 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888128 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 18558174 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888192 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888256 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 20360208 d112 d113
private def d107 : MobiusHarmonicTree := .branch 38918382 d108 d111
private def d99 : MobiusHarmonicTree := .branch 76875094 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888320 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888384 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 19376841 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888448 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888512 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 20672827 d120 d121
private def d115 : MobiusHarmonicTree := .branch 40049668 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888576 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888640 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 20210721 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888704 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888768 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 20638756 d127 d128
private def d122 : MobiusHarmonicTree := .branch 40849477 d123 d126
private def d114 : MobiusHarmonicTree := .branch 80899145 d115 d122
private def d98 : MobiusHarmonicTree := .branch 157774239 d99 d114
private def d66 : MobiusHarmonicTree := .branch 315707082 d67 d98
private def d2 : MobiusHarmonicTree := .branch 621914004 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888832 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888896 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 19445566 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 888960 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889024 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 19247006 d138 d139
private def d133 : MobiusHarmonicTree := .branch 38692572 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889088 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889152 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 19543400 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889216 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889280 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 21028308 d145 d146
private def d140 : MobiusHarmonicTree := .branch 40571708 d141 d144
private def d132 : MobiusHarmonicTree := .branch 79264280 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889344 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889408 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 22594871 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889472 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889536 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 22833344 d153 d154
private def d148 : MobiusHarmonicTree := .branch 45428215 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889600 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889664 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 22438872 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889728 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889792 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 20446462 d160 d161
private def d155 : MobiusHarmonicTree := .branch 42885334 d156 d159
private def d147 : MobiusHarmonicTree := .branch 88313549 d148 d155
private def d131 : MobiusHarmonicTree := .branch 167577829 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889856 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889920 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 19842318 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 889984 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890048 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 18975469 d169 d170
private def d164 : MobiusHarmonicTree := .branch 38817787 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890112 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890176 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 18515537 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890240 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890304 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 17150409 d176 d177
private def d171 : MobiusHarmonicTree := .branch 35665946 d172 d175
private def d163 : MobiusHarmonicTree := .branch 74483733 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890368 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890432 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 17469109 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890496 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890560 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 17489061 d184 d185
private def d179 : MobiusHarmonicTree := .branch 34958170 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890624 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890688 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 17638118 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890752 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890816 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 19072442 d191 d192
private def d186 : MobiusHarmonicTree := .branch 36710560 d187 d190
private def d178 : MobiusHarmonicTree := .branch 71668730 d179 d186
private def d162 : MobiusHarmonicTree := .branch 146152463 d163 d178
private def d130 : MobiusHarmonicTree := .branch 313730292 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890880 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 890944 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 19341365 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891008 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891072 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 18728079 d201 d202
private def d196 : MobiusHarmonicTree := .branch 38069444 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891136 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891200 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 18584008 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891264 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891328 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 18674442 d208 d209
private def d203 : MobiusHarmonicTree := .branch 37258450 d204 d207
private def d195 : MobiusHarmonicTree := .branch 75327894 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891392 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891456 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 20449746 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891520 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891584 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 21023308 d216 d217
private def d211 : MobiusHarmonicTree := .branch 41473054 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891648 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891712 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 22917794 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891776 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891840 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 22458111 d223 d224
private def d218 : MobiusHarmonicTree := .branch 45375905 d219 d222
private def d210 : MobiusHarmonicTree := .branch 86848959 d211 d218
private def d194 : MobiusHarmonicTree := .branch 162176853 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891904 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 891968 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 23151121 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892032 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892096 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 25334771 d232 d233
private def d227 : MobiusHarmonicTree := .branch 48485892 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892160 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892224 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 25647244 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892288 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892352 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 27140706 d239 d240
private def d234 : MobiusHarmonicTree := .branch 52787950 d235 d238
private def d226 : MobiusHarmonicTree := .branch 101273842 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892416 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892480 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 27141305 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892544 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892608 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 27090355 d247 d248
private def d242 : MobiusHarmonicTree := .branch 54231660 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892672 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892736 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 27708141 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892800 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock108 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892864 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 27436500 d254 d255
private def d249 : MobiusHarmonicTree := .branch 55144641 d250 d253
private def d241 : MobiusHarmonicTree := .branch 109376301 d242 d249
private def d225 : MobiusHarmonicTree := .branch 210650143 d226 d241
private def d193 : MobiusHarmonicTree := .branch 372826996 d194 d225
private def d129 : MobiusHarmonicTree := .branch 686557288 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1308471292 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892928 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 892992 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 27897299 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893056 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893120 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 28403858 d266 d267
private def d261 : MobiusHarmonicTree := .branch 56301157 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893184 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893248 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 29407360 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893312 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893376 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 31203048 d273 d274
private def d268 : MobiusHarmonicTree := .branch 60610408 d269 d272
private def d260 : MobiusHarmonicTree := .branch 116911565 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893440 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893504 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 30680429 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893568 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893632 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 29493210 d281 d282
private def d276 : MobiusHarmonicTree := .branch 60173639 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893696 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893760 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 29986881 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893824 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893888 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 29192791 d288 d289
private def d283 : MobiusHarmonicTree := .branch 59179672 d284 d287
private def d275 : MobiusHarmonicTree := .branch 119353311 d276 d283
private def d259 : MobiusHarmonicTree := .branch 236264876 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 893952 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894016 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 29251226 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894080 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894144 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 29039017 d297 d298
private def d292 : MobiusHarmonicTree := .branch 58290243 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894208 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894272 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 30851989 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894336 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894400 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 31381988 d304 d305
private def d299 : MobiusHarmonicTree := .branch 62233977 d300 d303
private def d291 : MobiusHarmonicTree := .branch 120524220 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894464 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894528 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 31606682 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894592 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894656 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 32256070 d312 d313
private def d307 : MobiusHarmonicTree := .branch 63862752 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894720 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894784 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 31538417 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894848 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894912 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 30750609 d319 d320
private def d314 : MobiusHarmonicTree := .branch 62289026 d315 d318
private def d306 : MobiusHarmonicTree := .branch 126151778 d307 d314
private def d290 : MobiusHarmonicTree := .branch 246675998 d291 d306
private def d258 : MobiusHarmonicTree := .branch 482940874 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 894976 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895040 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 30608758 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895104 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895168 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 30544053 d329 d330
private def d324 : MobiusHarmonicTree := .branch 61152811 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895232 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895296 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 31443287 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895360 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895424 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 31689005 d336 d337
private def d331 : MobiusHarmonicTree := .branch 63132292 d332 d335
private def d323 : MobiusHarmonicTree := .branch 124285103 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895488 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895552 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 31104920 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895616 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895680 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 32547392 d344 d345
private def d339 : MobiusHarmonicTree := .branch 63652312 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895744 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895808 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 33522892 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895872 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 895936 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 34245808 d351 d352
private def d346 : MobiusHarmonicTree := .branch 67768700 d347 d350
private def d338 : MobiusHarmonicTree := .branch 131421012 d339 d346
private def d322 : MobiusHarmonicTree := .branch 255706115 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896000 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896064 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 33918448 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896128 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896192 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 33634623 d360 d361
private def d355 : MobiusHarmonicTree := .branch 67553071 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896256 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896320 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 33335280 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896384 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896448 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 32600960 d367 d368
private def d362 : MobiusHarmonicTree := .branch 65936240 d363 d366
private def d354 : MobiusHarmonicTree := .branch 133489311 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896512 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896576 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 34177864 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896640 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896704 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 35314957 d375 d376
private def d370 : MobiusHarmonicTree := .branch 69492821 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896768 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896832 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 36020204 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896896 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896960 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 37869067 d382 d383
private def d377 : MobiusHarmonicTree := .branch 73889271 d378 d381
private def d369 : MobiusHarmonicTree := .branch 143382092 d370 d377
private def d353 : MobiusHarmonicTree := .branch 276871403 d354 d369
private def d321 : MobiusHarmonicTree := .branch 532577518 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1015518392 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897024 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897088 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 38680791 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897152 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897216 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 39253736 d393 d394
private def d388 : MobiusHarmonicTree := .branch 77934527 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897280 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897344 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 39903388 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897408 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897472 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 40160647 d400 d401
private def d395 : MobiusHarmonicTree := .branch 80064035 d396 d399
private def d387 : MobiusHarmonicTree := .branch 157998562 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897536 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897600 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 41640006 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897664 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897728 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 41759970 d408 d409
private def d403 : MobiusHarmonicTree := .branch 83399976 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897792 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897856 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 40663628 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897920 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 897984 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 39333761 d415 d416
private def d410 : MobiusHarmonicTree := .branch 79997389 d411 d414
private def d402 : MobiusHarmonicTree := .branch 163397365 d403 d410
private def d386 : MobiusHarmonicTree := .branch 321395927 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898048 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898112 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 39508522 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898176 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898240 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 40276625 d424 d425
private def d419 : MobiusHarmonicTree := .branch 79785147 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898304 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898368 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 40546949 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898432 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898496 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 38748175 d431 d432
private def d426 : MobiusHarmonicTree := .branch 79295124 d427 d430
private def d418 : MobiusHarmonicTree := .branch 159080271 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898560 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898624 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 38112804 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898688 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898752 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 38141855 d439 d440
private def d434 : MobiusHarmonicTree := .branch 76254659 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898816 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898880 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 37567948 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 898944 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899008 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 37875182 d446 d447
private def d441 : MobiusHarmonicTree := .branch 75443130 d442 d445
private def d433 : MobiusHarmonicTree := .branch 151697789 d434 d441
private def d417 : MobiusHarmonicTree := .branch 310778060 d418 d433
private def d385 : MobiusHarmonicTree := .branch 632173987 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899072 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899136 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 35012612 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899200 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899264 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 34755172 d456 d457
private def d451 : MobiusHarmonicTree := .branch 69767784 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899328 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899392 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 33882986 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899456 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899520 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 32803179 d463 d464
private def d458 : MobiusHarmonicTree := .branch 66686165 d459 d462
private def d450 : MobiusHarmonicTree := .branch 136453949 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899584 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899648 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 31056683 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899712 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899776 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 31907997 d471 d472
private def d466 : MobiusHarmonicTree := .branch 62964680 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899840 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899904 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 32660231 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 899968 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900032 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 32046737 d478 d479
private def d473 : MobiusHarmonicTree := .branch 64706968 d474 d477
private def d465 : MobiusHarmonicTree := .branch 127671648 d466 d473
private def d449 : MobiusHarmonicTree := .branch 264125597 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900096 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900160 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 32748694 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900224 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900288 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 32617422 d487 d488
private def d482 : MobiusHarmonicTree := .branch 65366116 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900352 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900416 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 30752549 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900480 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900544 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 30122960 d494 d495
private def d489 : MobiusHarmonicTree := .branch 60875509 d490 d493
private def d481 : MobiusHarmonicTree := .branch 126241625 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900608 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900672 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 31464361 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900736 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900800 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 32706532 d502 d503
private def d497 : MobiusHarmonicTree := .branch 64170893 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900864 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900928 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 33204742 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 900992 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock109 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901056 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 33015793 d509 d510
private def d504 : MobiusHarmonicTree := .branch 66220535 d505 d508
private def d496 : MobiusHarmonicTree := .branch 130391428 d497 d504
private def d480 : MobiusHarmonicTree := .branch 256633053 d481 d496
private def d448 : MobiusHarmonicTree := .branch 520758650 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1152932637 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2168451029 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3476922321 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 884736 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 884736 3476922321 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 884736 1308471292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 884736 621914004 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 884736 306206922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 884736 141912825 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 884736 68000776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 884736 33509216 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884736 16441090 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884864 17068126 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 884992 34491560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884992 17516481 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 885120 16975079 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 885248 73912049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 885248 37496010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 885248 18444389 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 885376 19051621 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 885504 36416039 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 885504 18802698 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 885632 17613341 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 885760 164294097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 885760 79283832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 885760 38142491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 885760 18106374 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 885888 20036117 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 886016 41141341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886016 20639315 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886144 20502026 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 886272 85010265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 886272 41769026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886272 20435878 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886400 21333148 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 886528 43241239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886528 21356006 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886656 21885233 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 886784 315707082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 886784 157932843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 886784 83069263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 886784 43163347 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886784 21354358 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 886912 21808989 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 887040 39905916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887040 20605377 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887168 19300539 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 887296 74863580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 887296 37667619 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887296 18863904 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887424 18803715 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 887552 37195961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887552 18485544 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887680 18710417 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 887808 157774239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 887808 76875094 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 887808 37956712 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887808 18775299 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 887936 19181413 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 888064 38918382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888064 18558174 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888192 20360208 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 888320 80899145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 888320 40049668 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888320 19376841 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888448 20672827 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 888576 40849477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888576 20210721 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888704 20638756 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 888832 686557288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 888832 313730292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 888832 167577829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 888832 79264280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 888832 38692572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888832 19445566 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 888960 19247006 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 889088 40571708 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889088 19543400 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889216 21028308 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 889344 88313549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 889344 45428215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889344 22594871 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889472 22833344 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 889600 42885334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889600 22438872 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889728 20446462 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 889856 146152463 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 889856 74483733 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 889856 38817787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889856 19842318 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 889984 18975469 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 890112 35665946 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 890112 18515537 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 890240 17150409 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 890368 71668730 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 890368 34958170 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 890368 17469109 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 890496 17489061 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 890624 36710560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 890624 17638118 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 890752 19072442 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 890880 372826996 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 890880 162176853 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 890880 75327894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 890880 38069444 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 890880 19341365 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891008 18728079 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 891136 37258450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891136 18584008 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891264 18674442 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 891392 86848959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 891392 41473054 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891392 20449746 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891520 21023308 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 891648 45375905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891648 22917794 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891776 22458111 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 891904 210650143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 891904 101273842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 891904 48485892 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 891904 23151121 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892032 25334771 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 892160 52787950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892160 25647244 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892288 27140706 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 892416 109376301 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 892416 54231660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892416 27141305 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892544 27090355 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 892672 55144641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892672 27708141 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892800 27436500 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 892928 2168451029 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 892928 1015518392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 892928 482940874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 892928 236264876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 892928 116911565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 892928 56301157 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 892928 27897299 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893056 28403858 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 893184 60610408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893184 29407360 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893312 31203048 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 893440 119353311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 893440 60173639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893440 30680429 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893568 29493210 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 893696 59179672 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893696 29986881 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893824 29192791 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 893952 246675998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 893952 120524220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 893952 58290243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 893952 29251226 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894080 29039017 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 894208 62233977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894208 30851989 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894336 31381988 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 894464 126151778 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 894464 63862752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894464 31606682 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894592 32256070 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 894720 62289026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894720 31538417 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894848 30750609 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 894976 532577518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 894976 255706115 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 894976 124285103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 894976 61152811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 894976 30608758 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 895104 30544053 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 895232 63132292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 895232 31443287 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 895360 31689005 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 895488 131421012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 895488 63652312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 895488 31104920 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 895616 32547392 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 895744 67768700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 895744 33522892 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 895872 34245808 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 896000 276871403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 896000 133489311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 896000 67553071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896000 33918448 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896128 33634623 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 896256 65936240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896256 33335280 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896384 32600960 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 896512 143382092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 896512 69492821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896512 34177864 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896640 35314957 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 896768 73889271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896768 36020204 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896896 37869067 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 897024 1152932637 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 897024 632173987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 897024 321395927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 897024 157998562 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 897024 77934527 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897024 38680791 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897152 39253736 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 897280 80064035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897280 39903388 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897408 40160647 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 897536 163397365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 897536 83399976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897536 41640006 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897664 41759970 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 897792 79997389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897792 40663628 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 897920 39333761 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 898048 310778060 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 898048 159080271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 898048 79785147 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898048 39508522 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898176 40276625 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 898304 79295124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898304 40546949 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898432 38748175 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 898560 151697789 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 898560 76254659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898560 38112804 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898688 38141855 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 898816 75443130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898816 37567948 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 898944 37875182 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 899072 520758650 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 899072 264125597 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 899072 136453949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 899072 69767784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899072 35012612 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899200 34755172 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 899328 66686165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899328 33882986 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899456 32803179 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 899584 127671648 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 899584 62964680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899584 31056683 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899712 31907997 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 899840 64706968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899840 32660231 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 899968 32046737 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 900096 256633053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 900096 126241625 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 900096 65366116 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900096 32748694 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900224 32617422 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 900352 60875509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900352 30752549 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900480 30122960 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 900608 130391428 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 900608 64170893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900608 31464361 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900736 32706532 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 900864 66220535 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900864 33204742 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 900992 33015793 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 884736 (MobiusHarmonicTree.branch 3476922321 mobiusHarmonicBlock108 mobiusHarmonicBlock109) = true := Helfgott.combined

#print axioms solution
