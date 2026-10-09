-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair043_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:34:49.891626+00:00
-- url     : https://prove2.me/submissions/f551628d-1217-4cd5-a9c9-c3d58df94745

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704512 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704576 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 34840905 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704640 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704704 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 35070079 d11 d12
private def d6 : MobiusHarmonicTree := .branch 69910984 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704768 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704832 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 34377124 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704896 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704960 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 34854497 d18 d19
private def d13 : MobiusHarmonicTree := .branch 69231621 d14 d17
private def d5 : MobiusHarmonicTree := .branch 139142605 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705024 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705088 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 33496681 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705152 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705216 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 32001649 d26 d27
private def d21 : MobiusHarmonicTree := .branch 65498330 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705280 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705344 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 30356892 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705408 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705472 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 28641928 d33 d34
private def d28 : MobiusHarmonicTree := .branch 58998820 d29 d32
private def d20 : MobiusHarmonicTree := .branch 124497150 d21 d28
private def d4 : MobiusHarmonicTree := .branch 263639755 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705536 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705600 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 29749195 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705664 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705728 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 30755587 d42 d43
private def d37 : MobiusHarmonicTree := .branch 60504782 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705792 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705856 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 30384484 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705920 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 705984 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 29653759 d49 d50
private def d44 : MobiusHarmonicTree := .branch 60038243 d45 d48
private def d36 : MobiusHarmonicTree := .branch 120543025 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706048 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706112 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 28189684 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706176 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706240 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 27458180 d57 d58
private def d52 : MobiusHarmonicTree := .branch 55647864 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706304 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706368 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 27768872 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706432 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706496 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 28590458 d64 d65
private def d59 : MobiusHarmonicTree := .branch 56359330 d60 d63
private def d51 : MobiusHarmonicTree := .branch 112007194 d52 d59
private def d35 : MobiusHarmonicTree := .branch 232550219 d36 d51
private def d3 : MobiusHarmonicTree := .branch 496189974 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706560 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706624 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 28578247 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706688 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706752 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 27347762 d74 d75
private def d69 : MobiusHarmonicTree := .branch 55926009 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706816 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706880 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 27006070 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 706944 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707008 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 26931884 d81 d82
private def d76 : MobiusHarmonicTree := .branch 53937954 d77 d80
private def d68 : MobiusHarmonicTree := .branch 109863963 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707072 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707136 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 26235509 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707200 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707264 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 26243445 d89 d90
private def d84 : MobiusHarmonicTree := .branch 52478954 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707328 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707392 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 26915834 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707456 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707520 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 27677030 d96 d97
private def d91 : MobiusHarmonicTree := .branch 54592864 d92 d95
private def d83 : MobiusHarmonicTree := .branch 107071818 d84 d91
private def d67 : MobiusHarmonicTree := .branch 216935781 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707584 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707648 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 26778933 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707712 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707776 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 26107190 d105 d106
private def d100 : MobiusHarmonicTree := .branch 52886123 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707840 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707904 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 27010793 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 707968 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708032 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 26107643 d112 d113
private def d107 : MobiusHarmonicTree := .branch 53118436 d108 d111
private def d99 : MobiusHarmonicTree := .branch 106004559 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708096 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708160 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 27724059 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708224 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708288 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 27673834 d120 d121
private def d115 : MobiusHarmonicTree := .branch 55397893 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708352 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708416 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 28590599 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708480 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708544 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 29652431 d127 d128
private def d122 : MobiusHarmonicTree := .branch 58243030 d123 d126
private def d114 : MobiusHarmonicTree := .branch 113640923 d115 d122
private def d98 : MobiusHarmonicTree := .branch 219645482 d99 d114
private def d66 : MobiusHarmonicTree := .branch 436581263 d67 d98
private def d2 : MobiusHarmonicTree := .branch 932771237 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708608 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708672 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 30935409 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708736 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708800 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 31135786 d138 d139
private def d133 : MobiusHarmonicTree := .branch 62071195 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708864 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708928 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 32406745 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 708992 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709056 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 32736591 d145 d146
private def d140 : MobiusHarmonicTree := .branch 65143336 d141 d144
private def d132 : MobiusHarmonicTree := .branch 127214531 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709120 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709184 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 31952325 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709248 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709312 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 31330428 d153 d154
private def d148 : MobiusHarmonicTree := .branch 63282753 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709376 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709440 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 32520125 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709504 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709568 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 30238218 d160 d161
private def d155 : MobiusHarmonicTree := .branch 62758343 d156 d159
private def d147 : MobiusHarmonicTree := .branch 126041096 d148 d155
private def d131 : MobiusHarmonicTree := .branch 253255627 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709632 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709696 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 29064675 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709760 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709824 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 27650609 d169 d170
private def d164 : MobiusHarmonicTree := .branch 56715284 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709888 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 709952 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 27190682 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710016 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710080 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 27188512 d176 d177
private def d171 : MobiusHarmonicTree := .branch 54379194 d172 d175
private def d163 : MobiusHarmonicTree := .branch 111094478 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710144 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710208 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 31114874 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710272 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710336 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 31758315 d184 d185
private def d179 : MobiusHarmonicTree := .branch 62873189 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710400 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710464 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 30290173 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710528 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710592 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 28646631 d191 d192
private def d186 : MobiusHarmonicTree := .branch 58936804 d187 d190
private def d178 : MobiusHarmonicTree := .branch 121809993 d179 d186
private def d162 : MobiusHarmonicTree := .branch 232904471 d163 d178
private def d130 : MobiusHarmonicTree := .branch 486160098 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710656 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710720 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 30384745 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710784 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710848 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 29328466 d201 d202
private def d196 : MobiusHarmonicTree := .branch 59713211 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710912 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 710976 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 28522858 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711040 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711104 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 28848184 d208 d209
private def d203 : MobiusHarmonicTree := .branch 57371042 d204 d207
private def d195 : MobiusHarmonicTree := .branch 117084253 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711168 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711232 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 28650341 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711296 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711360 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 28143393 d216 d217
private def d211 : MobiusHarmonicTree := .branch 56793734 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711424 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711488 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 27730692 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711552 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711616 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 27790353 d223 d224
private def d218 : MobiusHarmonicTree := .branch 55521045 d219 d222
private def d210 : MobiusHarmonicTree := .branch 112314779 d211 d218
private def d194 : MobiusHarmonicTree := .branch 229399032 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711680 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711744 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 25652621 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711808 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711872 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 24959620 d232 d233
private def d227 : MobiusHarmonicTree := .branch 50612241 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 711936 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712000 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 24346984 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712064 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712128 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 24105327 d239 d240
private def d234 : MobiusHarmonicTree := .branch 48452311 d235 d238
private def d226 : MobiusHarmonicTree := .branch 99064552 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712192 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712256 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 24214672 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712320 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712384 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 22204408 d247 d248
private def d242 : MobiusHarmonicTree := .branch 46419080 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712448 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712512 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 20963958 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712576 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock086 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712640 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 20151907 d254 d255
private def d249 : MobiusHarmonicTree := .branch 41115865 d250 d253
private def d241 : MobiusHarmonicTree := .branch 87534945 d242 d249
private def d225 : MobiusHarmonicTree := .branch 186599497 d226 d241
private def d193 : MobiusHarmonicTree := .branch 415998529 d194 d225
private def d129 : MobiusHarmonicTree := .branch 902158627 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1834929864 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712704 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712768 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 19474859 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712832 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712896 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 17884894 d266 d267
private def d261 : MobiusHarmonicTree := .branch 37359753 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 712960 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713024 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 17947537 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713088 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713152 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 19336795 d273 d274
private def d268 : MobiusHarmonicTree := .branch 37284332 d269 d272
private def d260 : MobiusHarmonicTree := .branch 74644085 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713216 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713280 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 17238787 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713344 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713408 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 13686540 d281 d282
private def d276 : MobiusHarmonicTree := .branch 30925327 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713472 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713536 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 11514571 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713600 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713664 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 11419992 d288 d289
private def d283 : MobiusHarmonicTree := .branch 22934563 d284 d287
private def d275 : MobiusHarmonicTree := .branch 53859890 d276 d283
private def d259 : MobiusHarmonicTree := .branch 128503975 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713728 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713792 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 13953673 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713856 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713920 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 14267786 d297 d298
private def d292 : MobiusHarmonicTree := .branch 28221459 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 713984 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714048 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 14922009 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714112 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714176 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 16204752 d304 d305
private def d299 : MobiusHarmonicTree := .branch 31126761 d300 d303
private def d291 : MobiusHarmonicTree := .branch 59348220 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714240 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714304 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 17673182 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714368 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714432 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 19691210 d312 d313
private def d307 : MobiusHarmonicTree := .branch 37364392 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714496 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714560 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 20747116 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714624 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714688 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 20110939 d319 d320
private def d314 : MobiusHarmonicTree := .branch 40858055 d315 d318
private def d306 : MobiusHarmonicTree := .branch 78222447 d307 d314
private def d290 : MobiusHarmonicTree := .branch 137570667 d291 d306
private def d258 : MobiusHarmonicTree := .branch 266074642 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714752 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714816 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 21050272 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714880 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 714944 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 19021176 d329 d330
private def d324 : MobiusHarmonicTree := .branch 40071448 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715008 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715072 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 19810670 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715136 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715200 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 19559676 d336 d337
private def d331 : MobiusHarmonicTree := .branch 39370346 d332 d335
private def d323 : MobiusHarmonicTree := .branch 79441794 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715264 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715328 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 20120872 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715392 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715456 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 21208941 d344 d345
private def d339 : MobiusHarmonicTree := .branch 41329813 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715520 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715584 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 20707593 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715648 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715712 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 22207337 d351 d352
private def d346 : MobiusHarmonicTree := .branch 42914930 d347 d350
private def d338 : MobiusHarmonicTree := .branch 84244743 d339 d346
private def d322 : MobiusHarmonicTree := .branch 163686537 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715776 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715840 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 20222516 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715904 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 715968 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 17457553 d360 d361
private def d355 : MobiusHarmonicTree := .branch 37680069 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716032 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716096 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 18137269 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716160 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716224 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 19651703 d367 d368
private def d362 : MobiusHarmonicTree := .branch 37788972 d363 d366
private def d354 : MobiusHarmonicTree := .branch 75469041 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716288 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716352 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 22283796 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716416 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716480 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 23612748 d375 d376
private def d370 : MobiusHarmonicTree := .branch 45896544 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716544 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716608 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 24087165 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716672 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716736 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 22156114 d382 d383
private def d377 : MobiusHarmonicTree := .branch 46243279 d378 d381
private def d369 : MobiusHarmonicTree := .branch 92139823 d370 d377
private def d353 : MobiusHarmonicTree := .branch 167608864 d354 d369
private def d321 : MobiusHarmonicTree := .branch 331295401 d322 d353
private def d257 : MobiusHarmonicTree := .branch 597370043 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716800 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716864 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 21571808 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716928 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 716992 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 20414563 d393 d394
private def d388 : MobiusHarmonicTree := .branch 41986371 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717056 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717120 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 19629999 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717184 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717248 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 20999783 d400 d401
private def d395 : MobiusHarmonicTree := .branch 40629782 d396 d399
private def d387 : MobiusHarmonicTree := .branch 82616153 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717312 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717376 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 20924930 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717440 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717504 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 23854922 d408 d409
private def d403 : MobiusHarmonicTree := .branch 44779852 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717568 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717632 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 24717525 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717696 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717760 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 24791064 d415 d416
private def d410 : MobiusHarmonicTree := .branch 49508589 d411 d414
private def d402 : MobiusHarmonicTree := .branch 94288441 d403 d410
private def d386 : MobiusHarmonicTree := .branch 176904594 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717824 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717888 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 27863744 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 717952 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718016 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 28874088 d424 d425
private def d419 : MobiusHarmonicTree := .branch 56737832 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718080 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718144 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 29325661 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718208 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718272 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 30180791 d431 d432
private def d426 : MobiusHarmonicTree := .branch 59506452 d427 d430
private def d418 : MobiusHarmonicTree := .branch 116244284 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718336 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718400 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 32280181 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718464 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718528 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 31083074 d439 d440
private def d434 : MobiusHarmonicTree := .branch 63363255 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718592 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718656 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 31218083 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718720 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718784 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 31110960 d446 d447
private def d441 : MobiusHarmonicTree := .branch 62329043 d442 d445
private def d433 : MobiusHarmonicTree := .branch 125692298 d434 d441
private def d417 : MobiusHarmonicTree := .branch 241936582 d418 d433
private def d385 : MobiusHarmonicTree := .branch 418841176 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718848 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718912 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 30094198 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 718976 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719040 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 28621593 d456 d457
private def d451 : MobiusHarmonicTree := .branch 58715791 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719104 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719168 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 29566178 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719232 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719296 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 28473765 d463 d464
private def d458 : MobiusHarmonicTree := .branch 58039943 d459 d462
private def d450 : MobiusHarmonicTree := .branch 116755734 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719360 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719424 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 29215127 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719488 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719552 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 29127934 d471 d472
private def d466 : MobiusHarmonicTree := .branch 58343061 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719616 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719680 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 27747148 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719744 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719808 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 26898932 d478 d479
private def d473 : MobiusHarmonicTree := .branch 54646080 d474 d477
private def d465 : MobiusHarmonicTree := .branch 112989141 d466 d473
private def d449 : MobiusHarmonicTree := .branch 229744875 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719872 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 719936 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 26373309 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720000 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720064 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 25771371 d487 d488
private def d482 : MobiusHarmonicTree := .branch 52144680 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720128 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720192 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 26859612 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720256 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720320 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 23425784 d494 d495
private def d489 : MobiusHarmonicTree := .branch 50285396 d490 d493
private def d481 : MobiusHarmonicTree := .branch 102430076 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720384 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720448 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 22655453 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720512 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720576 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 22094924 d502 d503
private def d497 : MobiusHarmonicTree := .branch 44750377 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720640 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720704 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 22246383 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720768 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock087 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720832 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 22134199 d509 d510
private def d504 : MobiusHarmonicTree := .branch 44380582 d505 d508
private def d496 : MobiusHarmonicTree := .branch 89130959 d497 d504
private def d480 : MobiusHarmonicTree := .branch 191561035 d481 d496
private def d448 : MobiusHarmonicTree := .branch 421305910 d449 d480
private def d384 : MobiusHarmonicTree := .branch 840147086 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1437517129 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3272446993 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 704512 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 704512 3272446993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 704512 1834929864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 704512 932771237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 704512 496189974 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 704512 263639755 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 704512 139142605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 704512 69910984 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704512 34840905 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704640 35070079 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 704768 69231621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704768 34377124 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 704896 34854497 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 705024 124497150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 705024 65498330 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705024 33496681 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705152 32001649 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 705280 58998820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705280 30356892 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705408 28641928 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 705536 232550219 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 705536 120543025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 705536 60504782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705536 29749195 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705664 30755587 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 705792 60038243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705792 30384484 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 705920 29653759 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 706048 112007194 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 706048 55647864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706048 28189684 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706176 27458180 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 706304 56359330 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706304 27768872 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706432 28590458 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 706560 436581263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 706560 216935781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 706560 109863963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 706560 55926009 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706560 28578247 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706688 27347762 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 706816 53937954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706816 27006070 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 706944 26931884 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 707072 107071818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 707072 52478954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707072 26235509 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707200 26243445 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 707328 54592864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707328 26915834 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707456 27677030 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 707584 219645482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 707584 106004559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 707584 52886123 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707584 26778933 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707712 26107190 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 707840 53118436 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707840 27010793 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 707968 26107643 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 708096 113640923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 708096 55397893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708096 27724059 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708224 27673834 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 708352 58243030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708352 28590599 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708480 29652431 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 708608 902158627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 708608 486160098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 708608 253255627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 708608 127214531 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 708608 62071195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708608 30935409 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708736 31135786 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 708864 65143336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708864 32406745 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 708992 32736591 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 709120 126041096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 709120 63282753 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 709120 31952325 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 709248 31330428 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 709376 62758343 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 709376 32520125 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 709504 30238218 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 709632 232904471 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 709632 111094478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 709632 56715284 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 709632 29064675 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 709760 27650609 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 709888 54379194 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 709888 27190682 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710016 27188512 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 710144 121809993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 710144 62873189 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710144 31114874 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710272 31758315 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 710400 58936804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710400 30290173 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710528 28646631 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 710656 415998529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 710656 229399032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 710656 117084253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 710656 59713211 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710656 30384745 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710784 29328466 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 710912 57371042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 710912 28522858 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711040 28848184 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 711168 112314779 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 711168 56793734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711168 28650341 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711296 28143393 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 711424 55521045 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711424 27730692 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711552 27790353 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 711680 186599497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 711680 99064552 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 711680 50612241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711680 25652621 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711808 24959620 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 711936 48452311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 711936 24346984 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712064 24105327 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 712192 87534945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 712192 46419080 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712192 24214672 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712320 22204408 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 712448 41115865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712448 20963958 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712576 20151907 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 712704 1437517129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 712704 597370043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 712704 266074642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 712704 128503975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 712704 74644085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 712704 37359753 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712704 19474859 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712832 17884894 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 712960 37284332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 712960 17947537 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713088 19336795 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 713216 53859890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 713216 30925327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713216 17238787 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713344 13686540 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 713472 22934563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713472 11514571 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713600 11419992 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 713728 137570667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 713728 59348220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 713728 28221459 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713728 13953673 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713856 14267786 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 713984 31126761 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 713984 14922009 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 714112 16204752 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 714240 78222447 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 714240 37364392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 714240 17673182 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 714368 19691210 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 714496 40858055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 714496 20747116 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 714624 20110939 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 714752 331295401 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 714752 163686537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 714752 79441794 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 714752 40071448 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 714752 21050272 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 714880 19021176 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 715008 39370346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715008 19810670 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715136 19559676 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 715264 84244743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 715264 41329813 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715264 20120872 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715392 21208941 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 715520 42914930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715520 20707593 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715648 22207337 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 715776 167608864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 715776 75469041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 715776 37680069 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715776 20222516 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 715904 17457553 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 716032 37788972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716032 18137269 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716160 19651703 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 716288 92139823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 716288 45896544 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716288 22283796 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716416 23612748 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 716544 46243279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716544 24087165 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716672 22156114 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 716800 840147086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 716800 418841176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 716800 176904594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 716800 82616153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 716800 41986371 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716800 21571808 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 716928 20414563 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 717056 40629782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717056 19629999 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717184 20999783 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 717312 94288441 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 717312 44779852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717312 20924930 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717440 23854922 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 717568 49508589 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717568 24717525 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717696 24791064 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 717824 241936582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 717824 116244284 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 717824 56737832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717824 27863744 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 717952 28874088 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 718080 59506452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718080 29325661 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718208 30180791 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 718336 125692298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 718336 63363255 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718336 32280181 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718464 31083074 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 718592 62329043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718592 31218083 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718720 31110960 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 718848 421305910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 718848 229744875 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 718848 116755734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 718848 58715791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718848 30094198 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 718976 28621593 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 719104 58039943 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 719104 29566178 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 719232 28473765 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 719360 112989141 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 719360 58343061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 719360 29215127 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 719488 29127934 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 719616 54646080 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 719616 27747148 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 719744 26898932 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 719872 191561035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 719872 102430076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 719872 52144680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 719872 26373309 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720000 25771371 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 720128 50285396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720128 26859612 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720256 23425784 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 720384 89130959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 720384 44750377 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720384 22655453 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720512 22094924 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 720640 44380582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720640 22246383 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720768 22134199 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 704512 (MobiusHarmonicTree.branch 3272446993 mobiusHarmonicBlock086 mobiusHarmonicBlock087) = true := Helfgott.combined

#print axioms solution
