-- Prove2me | solution 1 for Helfgott.mobiusValuePair073_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:15:56.041726+00:00
-- url     : https://prove2.me/submissions/9163d74b-454f-455a-a5eb-b5d68b3bf42f

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
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

private def publishedLeaf : ℕ → MobiusCertTree → ℕ → MobiusCertTree
  | 0, tree, _ => tree
  | d + 1, .branch l r, k =>
      if k < 2 ^ d then publishedLeaf d l k else publishedLeaf d r (k - 2 ^ d)
  | _, tree, _ => tree

private abbrev d8 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 0
private theorem p8 : mobiusTreeCheck cg 1200001 1 1196032 d8 = true := by decide +kernel

private abbrev d9 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 1
private theorem p9 : mobiusTreeCheck cg 1200001 1 1196096 d9 = true := by decide +kernel

private def d7 : MobiusCertTree := .branch d8 d9
private abbrev d11 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 2
private theorem p11 : mobiusTreeCheck cg 1200001 1 1196160 d11 = true := by decide +kernel

private abbrev d12 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 3
private theorem p12 : mobiusTreeCheck cg 1200001 1 1196224 d12 = true := by decide +kernel

private def d10 : MobiusCertTree := .branch d11 d12
private def d6 : MobiusCertTree := .branch d7 d10
private abbrev d15 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 4
private theorem p15 : mobiusTreeCheck cg 1200001 1 1196288 d15 = true := by decide +kernel

private abbrev d16 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 5
private theorem p16 : mobiusTreeCheck cg 1200001 1 1196352 d16 = true := by decide +kernel

private def d14 : MobiusCertTree := .branch d15 d16
private abbrev d18 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 6
private theorem p18 : mobiusTreeCheck cg 1200001 1 1196416 d18 = true := by decide +kernel

private abbrev d19 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 7
private theorem p19 : mobiusTreeCheck cg 1200001 1 1196480 d19 = true := by decide +kernel

private def d17 : MobiusCertTree := .branch d18 d19
private def d13 : MobiusCertTree := .branch d14 d17
private def d5 : MobiusCertTree := .branch d6 d13
private abbrev d23 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 8
private theorem p23 : mobiusTreeCheck cg 1200001 1 1196544 d23 = true := by decide +kernel

private abbrev d24 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 9
private theorem p24 : mobiusTreeCheck cg 1200001 1 1196608 d24 = true := by decide +kernel

private def d22 : MobiusCertTree := .branch d23 d24
private abbrev d26 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 10
private theorem p26 : mobiusTreeCheck cg 1200001 1 1196672 d26 = true := by decide +kernel

private abbrev d27 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 11
private theorem p27 : mobiusTreeCheck cg 1200001 1 1196736 d27 = true := by decide +kernel

private def d25 : MobiusCertTree := .branch d26 d27
private def d21 : MobiusCertTree := .branch d22 d25
private abbrev d30 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 12
private theorem p30 : mobiusTreeCheck cg 1200001 1 1196800 d30 = true := by decide +kernel

private abbrev d31 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 13
private theorem p31 : mobiusTreeCheck cg 1200001 1 1196864 d31 = true := by decide +kernel

private def d29 : MobiusCertTree := .branch d30 d31
private abbrev d33 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 14
private theorem p33 : mobiusTreeCheck cg 1200001 1 1196928 d33 = true := by decide +kernel

private abbrev d34 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 15
private theorem p34 : mobiusTreeCheck cg 1200001 1 1196992 d34 = true := by decide +kernel

private def d32 : MobiusCertTree := .branch d33 d34
private def d28 : MobiusCertTree := .branch d29 d32
private def d20 : MobiusCertTree := .branch d21 d28
private def d4 : MobiusCertTree := .branch d5 d20
private abbrev d39 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 16
private theorem p39 : mobiusTreeCheck cg 1200001 1 1197056 d39 = true := by decide +kernel

private abbrev d40 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 17
private theorem p40 : mobiusTreeCheck cg 1200001 1 1197120 d40 = true := by decide +kernel

private def d38 : MobiusCertTree := .branch d39 d40
private abbrev d42 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 18
private theorem p42 : mobiusTreeCheck cg 1200001 1 1197184 d42 = true := by decide +kernel

private abbrev d43 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 19
private theorem p43 : mobiusTreeCheck cg 1200001 1 1197248 d43 = true := by decide +kernel

private def d41 : MobiusCertTree := .branch d42 d43
private def d37 : MobiusCertTree := .branch d38 d41
private abbrev d46 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 20
private theorem p46 : mobiusTreeCheck cg 1200001 1 1197312 d46 = true := by decide +kernel

private abbrev d47 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 21
private theorem p47 : mobiusTreeCheck cg 1200001 1 1197376 d47 = true := by decide +kernel

private def d45 : MobiusCertTree := .branch d46 d47
private abbrev d49 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 22
private theorem p49 : mobiusTreeCheck cg 1200001 1 1197440 d49 = true := by decide +kernel

private abbrev d50 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 23
private theorem p50 : mobiusTreeCheck cg 1200001 1 1197504 d50 = true := by decide +kernel

private def d48 : MobiusCertTree := .branch d49 d50
private def d44 : MobiusCertTree := .branch d45 d48
private def d36 : MobiusCertTree := .branch d37 d44
private abbrev d54 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 24
private theorem p54 : mobiusTreeCheck cg 1200001 1 1197568 d54 = true := by decide +kernel

private abbrev d55 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 25
private theorem p55 : mobiusTreeCheck cg 1200001 1 1197632 d55 = true := by decide +kernel

private def d53 : MobiusCertTree := .branch d54 d55
private abbrev d57 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 26
private theorem p57 : mobiusTreeCheck cg 1200001 1 1197696 d57 = true := by decide +kernel

private abbrev d58 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 27
private theorem p58 : mobiusTreeCheck cg 1200001 1 1197760 d58 = true := by decide +kernel

private def d56 : MobiusCertTree := .branch d57 d58
private def d52 : MobiusCertTree := .branch d53 d56
private abbrev d61 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 28
private theorem p61 : mobiusTreeCheck cg 1200001 1 1197824 d61 = true := by decide +kernel

private abbrev d62 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 29
private theorem p62 : mobiusTreeCheck cg 1200001 1 1197888 d62 = true := by decide +kernel

private def d60 : MobiusCertTree := .branch d61 d62
private abbrev d64 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 30
private theorem p64 : mobiusTreeCheck cg 1200001 1 1197952 d64 = true := by decide +kernel

private abbrev d65 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 31
private theorem p65 : mobiusTreeCheck cg 1200001 1 1198016 d65 = true := by decide +kernel

private def d63 : MobiusCertTree := .branch d64 d65
private def d59 : MobiusCertTree := .branch d60 d63
private def d51 : MobiusCertTree := .branch d52 d59
private def d35 : MobiusCertTree := .branch d36 d51
private def d3 : MobiusCertTree := .branch d4 d35
private abbrev d71 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 32
private theorem p71 : mobiusTreeCheck cg 1200001 1 1198080 d71 = true := by decide +kernel

private abbrev d72 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 33
private theorem p72 : mobiusTreeCheck cg 1200001 1 1198144 d72 = true := by decide +kernel

private def d70 : MobiusCertTree := .branch d71 d72
private abbrev d74 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 34
private theorem p74 : mobiusTreeCheck cg 1200001 1 1198208 d74 = true := by decide +kernel

private abbrev d75 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 35
private theorem p75 : mobiusTreeCheck cg 1200001 1 1198272 d75 = true := by decide +kernel

private def d73 : MobiusCertTree := .branch d74 d75
private def d69 : MobiusCertTree := .branch d70 d73
private abbrev d78 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 36
private theorem p78 : mobiusTreeCheck cg 1200001 1 1198336 d78 = true := by decide +kernel

private abbrev d79 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 37
private theorem p79 : mobiusTreeCheck cg 1200001 1 1198400 d79 = true := by decide +kernel

private def d77 : MobiusCertTree := .branch d78 d79
private abbrev d81 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 38
private theorem p81 : mobiusTreeCheck cg 1200001 1 1198464 d81 = true := by decide +kernel

private abbrev d82 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 39
private theorem p82 : mobiusTreeCheck cg 1200001 1 1198528 d82 = true := by decide +kernel

private def d80 : MobiusCertTree := .branch d81 d82
private def d76 : MobiusCertTree := .branch d77 d80
private def d68 : MobiusCertTree := .branch d69 d76
private abbrev d86 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 40
private theorem p86 : mobiusTreeCheck cg 1200001 1 1198592 d86 = true := by decide +kernel

private abbrev d87 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 41
private theorem p87 : mobiusTreeCheck cg 1200001 1 1198656 d87 = true := by decide +kernel

private def d85 : MobiusCertTree := .branch d86 d87
private abbrev d89 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 42
private theorem p89 : mobiusTreeCheck cg 1200001 1 1198720 d89 = true := by decide +kernel

private abbrev d90 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 43
private theorem p90 : mobiusTreeCheck cg 1200001 1 1198784 d90 = true := by decide +kernel

private def d88 : MobiusCertTree := .branch d89 d90
private def d84 : MobiusCertTree := .branch d85 d88
private abbrev d93 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 44
private theorem p93 : mobiusTreeCheck cg 1200001 1 1198848 d93 = true := by decide +kernel

private abbrev d94 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 45
private theorem p94 : mobiusTreeCheck cg 1200001 1 1198912 d94 = true := by decide +kernel

private def d92 : MobiusCertTree := .branch d93 d94
private abbrev d96 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 46
private theorem p96 : mobiusTreeCheck cg 1200001 1 1198976 d96 = true := by decide +kernel

private abbrev d97 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 47
private theorem p97 : mobiusTreeCheck cg 1200001 1 1199040 d97 = true := by decide +kernel

private def d95 : MobiusCertTree := .branch d96 d97
private def d91 : MobiusCertTree := .branch d92 d95
private def d83 : MobiusCertTree := .branch d84 d91
private def d67 : MobiusCertTree := .branch d68 d83
private abbrev d102 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 48
private theorem p102 : mobiusTreeCheck cg 1200001 1 1199104 d102 = true := by decide +kernel

private abbrev d103 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 49
private theorem p103 : mobiusTreeCheck cg 1200001 1 1199168 d103 = true := by decide +kernel

private def d101 : MobiusCertTree := .branch d102 d103
private abbrev d105 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 50
private theorem p105 : mobiusTreeCheck cg 1200001 1 1199232 d105 = true := by decide +kernel

private abbrev d106 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 51
private theorem p106 : mobiusTreeCheck cg 1200001 1 1199296 d106 = true := by decide +kernel

private def d104 : MobiusCertTree := .branch d105 d106
private def d100 : MobiusCertTree := .branch d101 d104
private abbrev d109 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 52
private theorem p109 : mobiusTreeCheck cg 1200001 1 1199360 d109 = true := by decide +kernel

private abbrev d110 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 53
private theorem p110 : mobiusTreeCheck cg 1200001 1 1199424 d110 = true := by decide +kernel

private def d108 : MobiusCertTree := .branch d109 d110
private abbrev d112 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 54
private theorem p112 : mobiusTreeCheck cg 1200001 1 1199488 d112 = true := by decide +kernel

private abbrev d113 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 55
private theorem p113 : mobiusTreeCheck cg 1200001 1 1199552 d113 = true := by decide +kernel

private def d111 : MobiusCertTree := .branch d112 d113
private def d107 : MobiusCertTree := .branch d108 d111
private def d99 : MobiusCertTree := .branch d100 d107
private abbrev d117 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 56
private theorem p117 : mobiusTreeCheck cg 1200001 1 1199616 d117 = true := by decide +kernel

private abbrev d118 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 57
private theorem p118 : mobiusTreeCheck cg 1200001 1 1199680 d118 = true := by decide +kernel

private def d116 : MobiusCertTree := .branch d117 d118
private abbrev d120 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 58
private theorem p120 : mobiusTreeCheck cg 1200001 1 1199744 d120 = true := by decide +kernel

private abbrev d121 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 59
private theorem p121 : mobiusTreeCheck cg 1200001 1 1199808 d121 = true := by decide +kernel

private def d119 : MobiusCertTree := .branch d120 d121
private def d115 : MobiusCertTree := .branch d116 d119
private abbrev d124 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 60
private theorem p124 : mobiusTreeCheck cg 1200001 1 1199872 d124 = true := by decide +kernel

private abbrev d125 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 61
private theorem p125 : mobiusTreeCheck cg 1200001 1 1199936 d125 = true := by decide +kernel

private def d123 : MobiusCertTree := .branch d124 d125
private abbrev d127 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock146 62
private theorem p127 : mobiusTreeCheck cg 1200001 1 1200000 d127 = true := by decide +kernel

private def d128 : MobiusCertTree := .leaf 0 0
private theorem p128 : mobiusTreeCheck cg 1200001 1 1200064 d128 = true := by decide +kernel

private def d126 : MobiusCertTree := .branch d127 d128
private def d122 : MobiusCertTree := .branch d123 d126
private def d114 : MobiusCertTree := .branch d115 d122
private def d98 : MobiusCertTree := .branch d99 d114
private def d66 : MobiusCertTree := .branch d67 d98
private def d2 : MobiusCertTree := .branch d3 d66
private def d129 : MobiusCertTree := .leaf 0 0
private theorem p129 : mobiusTreeCheck cg 1200001 7 1200128 d129 = true := by decide +kernel

private def d1 : MobiusCertTree := .branch d2 d129
private def d130 : MobiusCertTree := .leaf 0 0
private theorem p130 : mobiusTreeCheck cg 1200001 8 1204224 d130 = true := by decide +kernel

private def d0 : MobiusCertTree := .branch d1 d130

private theorem combined : mobiusTreeCheck cg 1200001 9 1196032 d0 = true :=
  (mobiusTreeCheck_join cg 1200001 8 1196032 _ _ (mobiusTreeCheck_join cg 1200001 7 1196032 _ _ (mobiusTreeCheck_join cg 1200001 6 1196032 _ _ (mobiusTreeCheck_join cg 1200001 5 1196032 _ _ (mobiusTreeCheck_join cg 1200001 4 1196032 _ _ (mobiusTreeCheck_join cg 1200001 3 1196032 _ _ (mobiusTreeCheck_join cg 1200001 2 1196032 _ _ (mobiusTreeCheck_join cg 1200001 1 1196032 _ _ p8 p9) (mobiusTreeCheck_join cg 1200001 1 1196160 _ _ p11 p12)) (mobiusTreeCheck_join cg 1200001 2 1196288 _ _ (mobiusTreeCheck_join cg 1200001 1 1196288 _ _ p15 p16) (mobiusTreeCheck_join cg 1200001 1 1196416 _ _ p18 p19))) (mobiusTreeCheck_join cg 1200001 3 1196544 _ _ (mobiusTreeCheck_join cg 1200001 2 1196544 _ _ (mobiusTreeCheck_join cg 1200001 1 1196544 _ _ p23 p24) (mobiusTreeCheck_join cg 1200001 1 1196672 _ _ p26 p27)) (mobiusTreeCheck_join cg 1200001 2 1196800 _ _ (mobiusTreeCheck_join cg 1200001 1 1196800 _ _ p30 p31) (mobiusTreeCheck_join cg 1200001 1 1196928 _ _ p33 p34)))) (mobiusTreeCheck_join cg 1200001 4 1197056 _ _ (mobiusTreeCheck_join cg 1200001 3 1197056 _ _ (mobiusTreeCheck_join cg 1200001 2 1197056 _ _ (mobiusTreeCheck_join cg 1200001 1 1197056 _ _ p39 p40) (mobiusTreeCheck_join cg 1200001 1 1197184 _ _ p42 p43)) (mobiusTreeCheck_join cg 1200001 2 1197312 _ _ (mobiusTreeCheck_join cg 1200001 1 1197312 _ _ p46 p47) (mobiusTreeCheck_join cg 1200001 1 1197440 _ _ p49 p50))) (mobiusTreeCheck_join cg 1200001 3 1197568 _ _ (mobiusTreeCheck_join cg 1200001 2 1197568 _ _ (mobiusTreeCheck_join cg 1200001 1 1197568 _ _ p54 p55) (mobiusTreeCheck_join cg 1200001 1 1197696 _ _ p57 p58)) (mobiusTreeCheck_join cg 1200001 2 1197824 _ _ (mobiusTreeCheck_join cg 1200001 1 1197824 _ _ p61 p62) (mobiusTreeCheck_join cg 1200001 1 1197952 _ _ p64 p65))))) (mobiusTreeCheck_join cg 1200001 5 1198080 _ _ (mobiusTreeCheck_join cg 1200001 4 1198080 _ _ (mobiusTreeCheck_join cg 1200001 3 1198080 _ _ (mobiusTreeCheck_join cg 1200001 2 1198080 _ _ (mobiusTreeCheck_join cg 1200001 1 1198080 _ _ p71 p72) (mobiusTreeCheck_join cg 1200001 1 1198208 _ _ p74 p75)) (mobiusTreeCheck_join cg 1200001 2 1198336 _ _ (mobiusTreeCheck_join cg 1200001 1 1198336 _ _ p78 p79) (mobiusTreeCheck_join cg 1200001 1 1198464 _ _ p81 p82))) (mobiusTreeCheck_join cg 1200001 3 1198592 _ _ (mobiusTreeCheck_join cg 1200001 2 1198592 _ _ (mobiusTreeCheck_join cg 1200001 1 1198592 _ _ p86 p87) (mobiusTreeCheck_join cg 1200001 1 1198720 _ _ p89 p90)) (mobiusTreeCheck_join cg 1200001 2 1198848 _ _ (mobiusTreeCheck_join cg 1200001 1 1198848 _ _ p93 p94) (mobiusTreeCheck_join cg 1200001 1 1198976 _ _ p96 p97)))) (mobiusTreeCheck_join cg 1200001 4 1199104 _ _ (mobiusTreeCheck_join cg 1200001 3 1199104 _ _ (mobiusTreeCheck_join cg 1200001 2 1199104 _ _ (mobiusTreeCheck_join cg 1200001 1 1199104 _ _ p102 p103) (mobiusTreeCheck_join cg 1200001 1 1199232 _ _ p105 p106)) (mobiusTreeCheck_join cg 1200001 2 1199360 _ _ (mobiusTreeCheck_join cg 1200001 1 1199360 _ _ p109 p110) (mobiusTreeCheck_join cg 1200001 1 1199488 _ _ p112 p113))) (mobiusTreeCheck_join cg 1200001 3 1199616 _ _ (mobiusTreeCheck_join cg 1200001 2 1199616 _ _ (mobiusTreeCheck_join cg 1200001 1 1199616 _ _ p117 p118) (mobiusTreeCheck_join cg 1200001 1 1199744 _ _ p120 p121)) (mobiusTreeCheck_join cg 1200001 2 1199872 _ _ (mobiusTreeCheck_join cg 1200001 1 1199872 _ _ p124 p125) (mobiusTreeCheck_join cg 1200001 1 1200000 _ _ p127 p128)))))) p129) p130)

end Helfgott

open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1196032 (MobiusCertTree.branch mobiusTableBlock146 (MobiusCertTree.leaf 0 0)) = true := Helfgott.combined

#print axioms solution
