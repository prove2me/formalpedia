-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair058_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:27:46.795731+00:00
-- url     : https://prove2.me/submissions/8cee9c34-5c83-4c7f-a9de-77b07122e912

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950272 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950336 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 16363767 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950400 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950464 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 17112754 d11 d12
private def d6 : MobiusHarmonicTree := .branch 33476521 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950528 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950592 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 18423335 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950656 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950720 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 17381667 d18 d19
private def d13 : MobiusHarmonicTree := .branch 35805002 d14 d17
private def d5 : MobiusHarmonicTree := .branch 69281523 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950784 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950848 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 15530425 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950912 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950976 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 16126657 d26 d27
private def d21 : MobiusHarmonicTree := .branch 31657082 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951040 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951104 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 16718518 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951168 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951232 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 17399627 d33 d34
private def d28 : MobiusHarmonicTree := .branch 34118145 d29 d32
private def d20 : MobiusHarmonicTree := .branch 65775227 d21 d28
private def d4 : MobiusHarmonicTree := .branch 135056750 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951296 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951360 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 16576346 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951424 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951488 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 17261464 d42 d43
private def d37 : MobiusHarmonicTree := .branch 33837810 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951552 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951616 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 16840910 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951680 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951744 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 15483241 d49 d50
private def d44 : MobiusHarmonicTree := .branch 32324151 d45 d48
private def d36 : MobiusHarmonicTree := .branch 66161961 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951808 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951872 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 13823369 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 951936 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952000 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 13399249 d57 d58
private def d52 : MobiusHarmonicTree := .branch 27222618 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952064 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952128 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 11898679 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952192 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952256 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 12860064 d64 d65
private def d59 : MobiusHarmonicTree := .branch 24758743 d60 d63
private def d51 : MobiusHarmonicTree := .branch 51981361 d52 d59
private def d35 : MobiusHarmonicTree := .branch 118143322 d36 d51
private def d3 : MobiusHarmonicTree := .branch 253200072 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952320 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952384 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 12484519 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952448 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952512 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 13128499 d74 d75
private def d69 : MobiusHarmonicTree := .branch 25613018 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952576 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952640 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 15620847 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952704 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952768 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 16351392 d81 d82
private def d76 : MobiusHarmonicTree := .branch 31972239 d77 d80
private def d68 : MobiusHarmonicTree := .branch 57585257 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952832 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952896 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 14982826 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 952960 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953024 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 14779323 d89 d90
private def d84 : MobiusHarmonicTree := .branch 29762149 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953088 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953152 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 15491853 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953216 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953280 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 14942157 d96 d97
private def d91 : MobiusHarmonicTree := .branch 30434010 d92 d95
private def d83 : MobiusHarmonicTree := .branch 60196159 d84 d91
private def d67 : MobiusHarmonicTree := .branch 117781416 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953344 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953408 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 13357431 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953472 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953536 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 13151117 d105 d106
private def d100 : MobiusHarmonicTree := .branch 26508548 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953600 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953664 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 13285656 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953728 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953792 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 12595087 d112 d113
private def d107 : MobiusHarmonicTree := .branch 25880743 d108 d111
private def d99 : MobiusHarmonicTree := .branch 52389291 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953856 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953920 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 11703376 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 953984 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954048 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 10876877 d120 d121
private def d115 : MobiusHarmonicTree := .branch 22580253 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954112 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954176 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 12270324 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954240 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954304 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 13949509 d127 d128
private def d122 : MobiusHarmonicTree := .branch 26219833 d123 d126
private def d114 : MobiusHarmonicTree := .branch 48800086 d115 d122
private def d98 : MobiusHarmonicTree := .branch 101189377 d99 d114
private def d66 : MobiusHarmonicTree := .branch 218970793 d67 d98
private def d2 : MobiusHarmonicTree := .branch 472170865 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954368 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954432 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 15046713 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954496 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954560 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 14609950 d138 d139
private def d133 : MobiusHarmonicTree := .branch 29656663 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954624 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954688 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 13595077 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954752 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954816 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 13400574 d145 d146
private def d140 : MobiusHarmonicTree := .branch 26995651 d141 d144
private def d132 : MobiusHarmonicTree := .branch 56652314 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954880 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 954944 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 13491966 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955008 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955072 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 12477672 d153 d154
private def d148 : MobiusHarmonicTree := .branch 25969638 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955136 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955200 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 12250908 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955264 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955328 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 13655060 d160 d161
private def d155 : MobiusHarmonicTree := .branch 25905968 d156 d159
private def d147 : MobiusHarmonicTree := .branch 51875606 d148 d155
private def d131 : MobiusHarmonicTree := .branch 108527920 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955392 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955456 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 13809182 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955520 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955584 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 12646800 d169 d170
private def d164 : MobiusHarmonicTree := .branch 26455982 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955648 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955712 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 12134493 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955776 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955840 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 11342970 d176 d177
private def d171 : MobiusHarmonicTree := .branch 23477463 d172 d175
private def d163 : MobiusHarmonicTree := .branch 49933445 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955904 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 955968 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 11778701 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956032 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956096 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 11587832 d184 d185
private def d179 : MobiusHarmonicTree := .branch 23366533 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956160 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956224 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 9983096 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956288 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956352 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 10011021 d191 d192
private def d186 : MobiusHarmonicTree := .branch 19994117 d187 d190
private def d178 : MobiusHarmonicTree := .branch 43360650 d179 d186
private def d162 : MobiusHarmonicTree := .branch 93294095 d163 d178
private def d130 : MobiusHarmonicTree := .branch 201822015 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956416 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956480 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 9759833 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956544 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956608 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 8701644 d201 d202
private def d196 : MobiusHarmonicTree := .branch 18461477 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956672 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956736 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 8008566 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956800 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956864 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 6749218 d208 d209
private def d203 : MobiusHarmonicTree := .branch 14757784 d204 d207
private def d195 : MobiusHarmonicTree := .branch 33219261 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956928 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 956992 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 5101473 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957056 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957120 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 5937678 d216 d217
private def d211 : MobiusHarmonicTree := .branch 11039151 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957184 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957248 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 5165928 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957312 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957376 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 4409005 d223 d224
private def d218 : MobiusHarmonicTree := .branch 9574933 d219 d222
private def d210 : MobiusHarmonicTree := .branch 20614084 d211 d218
private def d194 : MobiusHarmonicTree := .branch 53833345 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957440 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957504 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 3949924 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957568 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957632 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 3053452 d232 d233
private def d227 : MobiusHarmonicTree := .branch 7003376 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957696 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957760 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 1278053 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957824 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957888 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 909346 d239 d240
private def d234 : MobiusHarmonicTree := .branch 2187399 d235 d238
private def d226 : MobiusHarmonicTree := .branch 9190775 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 957952 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958016 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 2408158 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958080 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958144 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 2443310 d247 d248
private def d242 : MobiusHarmonicTree := .branch 4851468 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958208 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958272 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 2511904 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958336 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock116 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958400 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 2147402 d254 d255
private def d249 : MobiusHarmonicTree := .branch 4659306 d250 d253
private def d241 : MobiusHarmonicTree := .branch 9510774 d242 d249
private def d225 : MobiusHarmonicTree := .branch 18701549 d226 d241
private def d193 : MobiusHarmonicTree := .branch 72534894 d194 d225
private def d129 : MobiusHarmonicTree := .branch 274356909 d130 d193
private def d1 : MobiusHarmonicTree := .branch 746527774 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958464 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958528 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 1955131 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958592 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958656 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 2499386 d266 d267
private def d261 : MobiusHarmonicTree := .branch 4454517 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958720 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958784 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 3211417 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958848 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958912 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 4641766 d273 d274
private def d268 : MobiusHarmonicTree := .branch 7853183 d269 d272
private def d260 : MobiusHarmonicTree := .branch 12307700 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 958976 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959040 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 3808077 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959104 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959168 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 2433430 d281 d282
private def d276 : MobiusHarmonicTree := .branch 6241507 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959232 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959296 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 3208642 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959360 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959424 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 5958842 d288 d289
private def d283 : MobiusHarmonicTree := .branch 9167484 d284 d287
private def d275 : MobiusHarmonicTree := .branch 15408991 d276 d283
private def d259 : MobiusHarmonicTree := .branch 27716691 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959488 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959552 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 5301505 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959616 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959680 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 5650918 d297 d298
private def d292 : MobiusHarmonicTree := .branch 10952423 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959744 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959808 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 3896702 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959872 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 959936 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 4526410 d304 d305
private def d299 : MobiusHarmonicTree := .branch 8423112 d300 d303
private def d291 : MobiusHarmonicTree := .branch 19375535 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960000 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960064 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 4114405 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960128 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960192 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 3173383 d312 d313
private def d307 : MobiusHarmonicTree := .branch 7287788 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960256 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960320 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 1373590 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960384 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960448 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 802795 d319 d320
private def d314 : MobiusHarmonicTree := .branch 2176385 d315 d318
private def d306 : MobiusHarmonicTree := .branch 9464173 d307 d314
private def d290 : MobiusHarmonicTree := .branch 28839708 d291 d306
private def d258 : MobiusHarmonicTree := .branch 56556399 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960512 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960576 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 639269 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960640 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960704 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 489270 d329 d330
private def d324 : MobiusHarmonicTree := .branch 1128539 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960768 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960832 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 861825 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960896 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960960 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 1895043 d336 d337
private def d331 : MobiusHarmonicTree := .branch 2756868 d332 d335
private def d323 : MobiusHarmonicTree := .branch 3885407 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961024 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961088 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 2504519 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961152 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961216 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 3031638 d344 d345
private def d339 : MobiusHarmonicTree := .branch 5536157 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961280 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961344 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 2635970 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961408 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961472 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 2846747 d351 d352
private def d346 : MobiusHarmonicTree := .branch 5482717 d347 d350
private def d338 : MobiusHarmonicTree := .branch 11018874 d339 d346
private def d322 : MobiusHarmonicTree := .branch 14904281 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961536 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961600 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 2671637 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961664 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961728 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 3127749 d360 d361
private def d355 : MobiusHarmonicTree := .branch 5799386 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961792 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961856 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 2649124 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961920 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 961984 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 2492832 d367 d368
private def d362 : MobiusHarmonicTree := .branch 5141956 d363 d366
private def d354 : MobiusHarmonicTree := .branch 10941342 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962048 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962112 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 2730521 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962176 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962240 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 2709377 d375 d376
private def d370 : MobiusHarmonicTree := .branch 5439898 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962304 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962368 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 2858639 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962432 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962496 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 2284759 d382 d383
private def d377 : MobiusHarmonicTree := .branch 5143398 d378 d381
private def d369 : MobiusHarmonicTree := .branch 10583296 d370 d377
private def d353 : MobiusHarmonicTree := .branch 21524638 d354 d369
private def d321 : MobiusHarmonicTree := .branch 36428919 d322 d353
private def d257 : MobiusHarmonicTree := .branch 92985318 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962560 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962624 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 1842952 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962688 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962752 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 1419945 d393 d394
private def d388 : MobiusHarmonicTree := .branch 3262897 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962816 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962880 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 1834155 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 962944 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963008 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 899341 d400 d401
private def d395 : MobiusHarmonicTree := .branch 2733496 d396 d399
private def d387 : MobiusHarmonicTree := .branch 5996393 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963072 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963136 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 601222 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963200 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963264 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 323984 d408 d409
private def d403 : MobiusHarmonicTree := .branch 925206 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963328 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963392 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 387228 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963456 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963520 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 940338 d415 d416
private def d410 : MobiusHarmonicTree := .branch 1327566 d411 d414
private def d402 : MobiusHarmonicTree := .branch 2252772 d403 d410
private def d386 : MobiusHarmonicTree := .branch 8249165 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963584 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963648 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 808467 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963712 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963776 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 699375 d424 d425
private def d419 : MobiusHarmonicTree := .branch 1507842 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963840 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963904 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 2260668 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 963968 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964032 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 744858 d431 d432
private def d426 : MobiusHarmonicTree := .branch 3005526 d427 d430
private def d418 : MobiusHarmonicTree := .branch 4513368 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964096 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964160 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 1215625 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964224 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964288 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 879488 d439 d440
private def d434 : MobiusHarmonicTree := .branch 2095113 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964352 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964416 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 728973 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964480 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964544 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 539173 d446 d447
private def d441 : MobiusHarmonicTree := .branch 1268146 d442 d445
private def d433 : MobiusHarmonicTree := .branch 3363259 d434 d441
private def d417 : MobiusHarmonicTree := .branch 7876627 d418 d433
private def d385 : MobiusHarmonicTree := .branch 16125792 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964608 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964672 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 745414 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964736 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964800 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 318251 d456 d457
private def d451 : MobiusHarmonicTree := .branch 1063665 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964864 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964928 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 425999 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 964992 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965056 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 220779 d463 d464
private def d458 : MobiusHarmonicTree := .branch 646778 d459 d462
private def d450 : MobiusHarmonicTree := .branch 1710443 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965120 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965184 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 979148 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965248 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965312 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 1002849 d471 d472
private def d466 : MobiusHarmonicTree := .branch 1981997 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965376 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965440 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 1203637 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965504 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965568 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 2974488 d478 d479
private def d473 : MobiusHarmonicTree := .branch 4178125 d474 d477
private def d465 : MobiusHarmonicTree := .branch 6160122 d466 d473
private def d449 : MobiusHarmonicTree := .branch 7870565 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965632 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965696 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 3392404 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965760 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965824 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 4543333 d487 d488
private def d482 : MobiusHarmonicTree := .branch 7935737 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965888 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 965952 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 4731149 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966016 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966080 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 4468631 d494 d495
private def d489 : MobiusHarmonicTree := .branch 9199780 d490 d493
private def d481 : MobiusHarmonicTree := .branch 17135517 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966144 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966208 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 5598237 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966272 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966336 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 5167016 d502 d503
private def d497 : MobiusHarmonicTree := .branch 10765253 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966400 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966464 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 4147134 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966528 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock117 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966592 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 4233500 d509 d510
private def d504 : MobiusHarmonicTree := .branch 8380634 d505 d508
private def d496 : MobiusHarmonicTree := .branch 19145887 d497 d504
private def d480 : MobiusHarmonicTree := .branch 36281404 d481 d496
private def d448 : MobiusHarmonicTree := .branch 44151969 d449 d480
private def d384 : MobiusHarmonicTree := .branch 60277761 d385 d448
private def d256 : MobiusHarmonicTree := .branch 153263079 d257 d384
private def d0 : MobiusHarmonicTree := .branch 899790853 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 950272 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 950272 899790853 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 950272 746527774 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 950272 472170865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 950272 253200072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 950272 135056750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 950272 69281523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 950272 33476521 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950272 16363767 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950400 17112754 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 950528 35805002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950528 18423335 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950656 17381667 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 950784 65775227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 950784 31657082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950784 15530425 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950912 16126657 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 951040 34118145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951040 16718518 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951168 17399627 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 951296 118143322 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 951296 66161961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 951296 33837810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951296 16576346 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951424 17261464 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 951552 32324151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951552 16840910 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951680 15483241 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 951808 51981361 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 951808 27222618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951808 13823369 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 951936 13399249 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 952064 24758743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952064 11898679 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952192 12860064 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 952320 218970793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 952320 117781416 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 952320 57585257 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 952320 25613018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952320 12484519 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952448 13128499 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 952576 31972239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952576 15620847 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952704 16351392 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 952832 60196159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 952832 29762149 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952832 14982826 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 952960 14779323 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 953088 30434010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953088 15491853 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953216 14942157 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 953344 101189377 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 953344 52389291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 953344 26508548 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953344 13357431 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953472 13151117 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 953600 25880743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953600 13285656 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953728 12595087 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 953856 48800086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 953856 22580253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953856 11703376 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 953984 10876877 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 954112 26219833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 954112 12270324 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 954240 13949509 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 954368 274356909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 954368 201822015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 954368 108527920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 954368 56652314 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 954368 29656663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 954368 15046713 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 954496 14609950 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 954624 26995651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 954624 13595077 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 954752 13400574 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 954880 51875606 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 954880 25969638 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 954880 13491966 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955008 12477672 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 955136 25905968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955136 12250908 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955264 13655060 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 955392 93294095 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 955392 49933445 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 955392 26455982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955392 13809182 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955520 12646800 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 955648 23477463 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955648 12134493 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955776 11342970 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 955904 43360650 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 955904 23366533 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 955904 11778701 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956032 11587832 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 956160 19994117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956160 9983096 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956288 10011021 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 956416 72534894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 956416 53833345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 956416 33219261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 956416 18461477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956416 9759833 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956544 8701644 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 956672 14757784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956672 8008566 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956800 6749218 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 956928 20614084 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 956928 11039151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 956928 5101473 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957056 5937678 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 957184 9574933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957184 5165928 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957312 4409005 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 957440 18701549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 957440 9190775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 957440 7003376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957440 3949924 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957568 3053452 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 957696 2187399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957696 1278053 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957824 909346 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 957952 9510774 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 957952 4851468 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 957952 2408158 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958080 2443310 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 958208 4659306 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958208 2511904 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958336 2147402 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 958464 153263079 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 958464 92985318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 958464 56556399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 958464 27716691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 958464 12307700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 958464 4454517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958464 1955131 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958592 2499386 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 958720 7853183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958720 3211417 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958848 4641766 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 958976 15408991 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 958976 6241507 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 958976 3808077 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 959104 2433430 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 959232 9167484 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 959232 3208642 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 959360 5958842 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 959488 28839708 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 959488 19375535 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 959488 10952423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 959488 5301505 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 959616 5650918 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 959744 8423112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 959744 3896702 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 959872 4526410 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 960000 9464173 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 960000 7287788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960000 4114405 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960128 3173383 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 960256 2176385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960256 1373590 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960384 802795 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 960512 36428919 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 960512 14904281 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 960512 3885407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 960512 1128539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960512 639269 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960640 489270 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 960768 2756868 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960768 861825 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 960896 1895043 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 961024 11018874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 961024 5536157 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961024 2504519 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961152 3031638 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 961280 5482717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961280 2635970 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961408 2846747 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 961536 21524638 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 961536 10941342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 961536 5799386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961536 2671637 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961664 3127749 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 961792 5141956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961792 2649124 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 961920 2492832 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 962048 10583296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 962048 5439898 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962048 2730521 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962176 2709377 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 962304 5143398 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962304 2858639 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962432 2284759 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 962560 60277761 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 962560 16125792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 962560 8249165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 962560 5996393 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 962560 3262897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962560 1842952 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962688 1419945 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 962816 2733496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962816 1834155 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 962944 899341 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 963072 2252772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 963072 925206 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963072 601222 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963200 323984 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 963328 1327566 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963328 387228 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963456 940338 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 963584 7876627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 963584 4513368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 963584 1507842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963584 808467 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963712 699375 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 963840 3005526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963840 2260668 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 963968 744858 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 964096 3363259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 964096 2095113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964096 1215625 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964224 879488 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 964352 1268146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964352 728973 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964480 539173 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 964608 44151969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 964608 7870565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 964608 1710443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 964608 1063665 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964608 745414 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964736 318251 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 964864 646778 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964864 425999 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 964992 220779 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 965120 6160122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 965120 1981997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 965120 979148 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 965248 1002849 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 965376 4178125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 965376 1203637 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 965504 2974488 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 965632 36281404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 965632 17135517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 965632 7935737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 965632 3392404 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 965760 4543333 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 965888 9199780 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 965888 4731149 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966016 4468631 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 966144 19145887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 966144 10765253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966144 5598237 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966272 5167016 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 966400 8380634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966400 4147134 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966528 4233500 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 950272 (MobiusHarmonicTree.branch 899790853 mobiusHarmonicBlock116 mobiusHarmonicBlock117) = true := Helfgott.combined

#print axioms solution
