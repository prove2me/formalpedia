-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair059_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:34:18.518988+00:00
-- url     : https://prove2.me/submissions/3325e4a2-5037-4609-82bc-52c69507f8dc

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966656 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966720 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 5282856 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966784 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966848 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 7402463 d11 d12
private def d6 : MobiusHarmonicTree := .branch 12685319 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966912 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 966976 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 7072632 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967040 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967104 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 7612478 d18 d19
private def d13 : MobiusHarmonicTree := .branch 14685110 d14 d17
private def d5 : MobiusHarmonicTree := .branch 27370429 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967168 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967232 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 7894746 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967296 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967360 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 8758967 d26 d27
private def d21 : MobiusHarmonicTree := .branch 16653713 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967424 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967488 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 8330914 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967552 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967616 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 9208262 d33 d34
private def d28 : MobiusHarmonicTree := .branch 17539176 d29 d32
private def d20 : MobiusHarmonicTree := .branch 34192889 d21 d28
private def d4 : MobiusHarmonicTree := .branch 61563318 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967680 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967744 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 9730940 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967808 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967872 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 9519893 d42 d43
private def d37 : MobiusHarmonicTree := .branch 19250833 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 967936 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968000 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 10607515 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968064 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968128 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 10392292 d49 d50
private def d44 : MobiusHarmonicTree := .branch 20999807 d45 d48
private def d36 : MobiusHarmonicTree := .branch 40250640 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968192 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968256 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 9821860 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968320 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968384 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 9908324 d57 d58
private def d52 : MobiusHarmonicTree := .branch 19730184 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968448 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968512 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 8736174 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968576 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968640 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 8345793 d64 d65
private def d59 : MobiusHarmonicTree := .branch 17081967 d60 d63
private def d51 : MobiusHarmonicTree := .branch 36812151 d52 d59
private def d35 : MobiusHarmonicTree := .branch 77062791 d36 d51
private def d3 : MobiusHarmonicTree := .branch 138626109 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968704 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968768 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 8711123 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968832 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968896 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 9553211 d74 d75
private def d69 : MobiusHarmonicTree := .branch 18264334 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 968960 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969024 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 9860500 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969088 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969152 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 8814999 d81 d82
private def d76 : MobiusHarmonicTree := .branch 18675499 d77 d80
private def d68 : MobiusHarmonicTree := .branch 36939833 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969216 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969280 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 10495475 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969344 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969408 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 9620385 d89 d90
private def d84 : MobiusHarmonicTree := .branch 20115860 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969472 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969536 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 7920355 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969600 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969664 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 7745034 d96 d97
private def d91 : MobiusHarmonicTree := .branch 15665389 d92 d95
private def d83 : MobiusHarmonicTree := .branch 35781249 d84 d91
private def d67 : MobiusHarmonicTree := .branch 72721082 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969728 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969792 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 7301640 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969856 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969920 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 4347878 d105 d106
private def d100 : MobiusHarmonicTree := .branch 11649518 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 969984 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970048 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 3492690 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970112 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970176 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 4696110 d112 d113
private def d107 : MobiusHarmonicTree := .branch 8188800 d108 d111
private def d99 : MobiusHarmonicTree := .branch 19838318 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970240 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970304 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 3892669 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970368 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970432 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 3971498 d120 d121
private def d115 : MobiusHarmonicTree := .branch 7864167 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970496 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970560 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 3740183 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970624 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970688 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 2950560 d127 d128
private def d122 : MobiusHarmonicTree := .branch 6690743 d123 d126
private def d114 : MobiusHarmonicTree := .branch 14554910 d115 d122
private def d98 : MobiusHarmonicTree := .branch 34393228 d99 d114
private def d66 : MobiusHarmonicTree := .branch 107114310 d67 d98
private def d2 : MobiusHarmonicTree := .branch 245740419 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970752 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970816 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 3340548 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970880 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 970944 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 2804587 d138 d139
private def d133 : MobiusHarmonicTree := .branch 6145135 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971008 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971072 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 831109 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971136 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971200 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 1341701 d145 d146
private def d140 : MobiusHarmonicTree := .branch 2172810 d141 d144
private def d132 : MobiusHarmonicTree := .branch 8317945 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971264 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971328 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 433490 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971392 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971456 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 331509 d153 d154
private def d148 : MobiusHarmonicTree := .branch 764999 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971520 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971584 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 1055036 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971648 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971712 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 2845518 d160 d161
private def d155 : MobiusHarmonicTree := .branch 3900554 d156 d159
private def d147 : MobiusHarmonicTree := .branch 4665553 d148 d155
private def d131 : MobiusHarmonicTree := .branch 12983498 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971776 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971840 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 3599417 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971904 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 971968 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 4611299 d169 d170
private def d164 : MobiusHarmonicTree := .branch 8210716 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972032 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972096 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 6678421 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972160 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972224 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 7184632 d176 d177
private def d171 : MobiusHarmonicTree := .branch 13863053 d172 d175
private def d163 : MobiusHarmonicTree := .branch 22073769 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972288 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972352 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 7055118 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972416 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972480 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 7054207 d184 d185
private def d179 : MobiusHarmonicTree := .branch 14109325 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972544 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972608 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6640977 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972672 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972736 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 5829000 d191 d192
private def d186 : MobiusHarmonicTree := .branch 12469977 d187 d190
private def d178 : MobiusHarmonicTree := .branch 26579302 d179 d186
private def d162 : MobiusHarmonicTree := .branch 48653071 d163 d178
private def d130 : MobiusHarmonicTree := .branch 61636569 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972800 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972864 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 5782974 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972928 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 972992 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 6064872 d201 d202
private def d196 : MobiusHarmonicTree := .branch 11847846 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973056 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973120 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 6186373 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973184 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973248 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 5015235 d208 d209
private def d203 : MobiusHarmonicTree := .branch 11201608 d204 d207
private def d195 : MobiusHarmonicTree := .branch 23049454 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973312 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973376 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 3859849 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973440 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973504 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 2465401 d216 d217
private def d211 : MobiusHarmonicTree := .branch 6325250 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973568 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973632 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 759107 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973696 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973760 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 821613 d223 d224
private def d218 : MobiusHarmonicTree := .branch 1580720 d219 d222
private def d210 : MobiusHarmonicTree := .branch 7905970 d211 d218
private def d194 : MobiusHarmonicTree := .branch 30955424 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973824 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973888 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 1230175 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 973952 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974016 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 3244358 d232 d233
private def d227 : MobiusHarmonicTree := .branch 4474533 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974080 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974144 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 4308455 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974208 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974272 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 4715409 d239 d240
private def d234 : MobiusHarmonicTree := .branch 9023864 d235 d238
private def d226 : MobiusHarmonicTree := .branch 13498397 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974336 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974400 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 3871163 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974464 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974528 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 2953306 d247 d248
private def d242 : MobiusHarmonicTree := .branch 6824469 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974592 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974656 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 2653298 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974720 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock118 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974784 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 2717589 d254 d255
private def d249 : MobiusHarmonicTree := .branch 5370887 d250 d253
private def d241 : MobiusHarmonicTree := .branch 12195356 d242 d249
private def d225 : MobiusHarmonicTree := .branch 25693753 d226 d241
private def d193 : MobiusHarmonicTree := .branch 56649177 d194 d225
private def d129 : MobiusHarmonicTree := .branch 118285746 d130 d193
private def d1 : MobiusHarmonicTree := .branch 364026165 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974848 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974912 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 4744053 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 974976 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975040 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 4081961 d266 d267
private def d261 : MobiusHarmonicTree := .branch 8826014 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975104 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975168 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 4378804 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975232 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975296 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 4905255 d273 d274
private def d268 : MobiusHarmonicTree := .branch 9284059 d269 d272
private def d260 : MobiusHarmonicTree := .branch 18110073 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975360 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975424 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 5074770 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975488 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975552 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 6158637 d281 d282
private def d276 : MobiusHarmonicTree := .branch 11233407 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975616 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975680 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 7180690 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975744 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975808 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 7662432 d288 d289
private def d283 : MobiusHarmonicTree := .branch 14843122 d284 d287
private def d275 : MobiusHarmonicTree := .branch 26076529 d276 d283
private def d259 : MobiusHarmonicTree := .branch 44186602 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975872 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 975936 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 6528172 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976000 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976064 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 5708722 d297 d298
private def d292 : MobiusHarmonicTree := .branch 12236894 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976128 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976192 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 3912238 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976256 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976320 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 3648454 d304 d305
private def d299 : MobiusHarmonicTree := .branch 7560692 d300 d303
private def d291 : MobiusHarmonicTree := .branch 19797586 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976384 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976448 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 4890251 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976512 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976576 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 4050955 d312 d313
private def d307 : MobiusHarmonicTree := .branch 8941206 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976640 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976704 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 5050721 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976768 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976832 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 5569094 d319 d320
private def d314 : MobiusHarmonicTree := .branch 10619815 d315 d318
private def d306 : MobiusHarmonicTree := .branch 19561021 d307 d314
private def d290 : MobiusHarmonicTree := .branch 39358607 d291 d306
private def d258 : MobiusHarmonicTree := .branch 83545209 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976896 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 976960 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 5619548 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977024 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977088 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 5831666 d329 d330
private def d324 : MobiusHarmonicTree := .branch 11451214 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977152 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977216 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 5707097 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977280 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977344 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 6582186 d336 d337
private def d331 : MobiusHarmonicTree := .branch 12289283 d332 d335
private def d323 : MobiusHarmonicTree := .branch 23740497 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977408 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977472 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 7744522 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977536 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977600 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 8089262 d344 d345
private def d339 : MobiusHarmonicTree := .branch 15833784 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977664 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977728 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 9738968 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977792 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977856 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 9373644 d351 d352
private def d346 : MobiusHarmonicTree := .branch 19112612 d347 d350
private def d338 : MobiusHarmonicTree := .branch 34946396 d339 d346
private def d322 : MobiusHarmonicTree := .branch 58686893 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977920 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 977984 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 9873442 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978048 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978112 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 8463320 d360 d361
private def d355 : MobiusHarmonicTree := .branch 18336762 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978176 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978240 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 8401880 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978304 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978368 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 9383050 d367 d368
private def d362 : MobiusHarmonicTree := .branch 17784930 d363 d366
private def d354 : MobiusHarmonicTree := .branch 36121692 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978432 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978496 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 10070612 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978560 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978624 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 11275078 d375 d376
private def d370 : MobiusHarmonicTree := .branch 21345690 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978688 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978752 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 11545377 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978816 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978880 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 11532651 d382 d383
private def d377 : MobiusHarmonicTree := .branch 23078028 d378 d381
private def d369 : MobiusHarmonicTree := .branch 44423718 d370 d377
private def d353 : MobiusHarmonicTree := .branch 80545410 d354 d369
private def d321 : MobiusHarmonicTree := .branch 139232303 d322 d353
private def d257 : MobiusHarmonicTree := .branch 222777512 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 978944 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979008 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 10964234 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979072 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979136 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 11073109 d393 d394
private def d388 : MobiusHarmonicTree := .branch 22037343 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979200 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979264 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 10537580 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979328 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979392 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 9969528 d400 d401
private def d395 : MobiusHarmonicTree := .branch 20507108 d396 d399
private def d387 : MobiusHarmonicTree := .branch 42544451 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979456 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979520 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 9312816 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979584 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979648 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 10780430 d408 d409
private def d403 : MobiusHarmonicTree := .branch 20093246 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979712 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979776 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 12797877 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979840 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979904 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 13262605 d415 d416
private def d410 : MobiusHarmonicTree := .branch 26060482 d411 d414
private def d402 : MobiusHarmonicTree := .branch 46153728 d403 d410
private def d386 : MobiusHarmonicTree := .branch 88698179 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 979968 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980032 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 14296518 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980096 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980160 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 14120233 d424 d425
private def d419 : MobiusHarmonicTree := .branch 28416751 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980224 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980288 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 15289437 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980352 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980416 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 15915775 d431 d432
private def d426 : MobiusHarmonicTree := .branch 31205212 d427 d430
private def d418 : MobiusHarmonicTree := .branch 59621963 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980480 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980544 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 15681172 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980608 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980672 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 15122356 d439 d440
private def d434 : MobiusHarmonicTree := .branch 30803528 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980736 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980800 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 15110176 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980864 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980928 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 14530210 d446 d447
private def d441 : MobiusHarmonicTree := .branch 29640386 d442 d445
private def d433 : MobiusHarmonicTree := .branch 60443914 d434 d441
private def d417 : MobiusHarmonicTree := .branch 120065877 d418 d433
private def d385 : MobiusHarmonicTree := .branch 208764056 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 980992 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981056 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 14011515 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981120 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981184 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 14061656 d456 d457
private def d451 : MobiusHarmonicTree := .branch 28073171 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981248 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981312 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 13875370 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981376 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981440 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 13801235 d463 d464
private def d458 : MobiusHarmonicTree := .branch 27676605 d459 d462
private def d450 : MobiusHarmonicTree := .branch 55749776 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981504 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981568 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 14195716 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981632 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981696 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 14273330 d471 d472
private def d466 : MobiusHarmonicTree := .branch 28469046 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981760 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981824 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 13465823 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981888 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 981952 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 14404036 d478 d479
private def d473 : MobiusHarmonicTree := .branch 27869859 d474 d477
private def d465 : MobiusHarmonicTree := .branch 56338905 d466 d473
private def d449 : MobiusHarmonicTree := .branch 112088681 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982016 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982080 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 14275937 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982144 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982208 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 12358962 d487 d488
private def d482 : MobiusHarmonicTree := .branch 26634899 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982272 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982336 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 13419091 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982400 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982464 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 14990927 d494 d495
private def d489 : MobiusHarmonicTree := .branch 28410018 d490 d493
private def d481 : MobiusHarmonicTree := .branch 55044917 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982528 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982592 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 16660086 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982656 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982720 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 18489541 d502 d503
private def d497 : MobiusHarmonicTree := .branch 35149627 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982784 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982848 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 19161741 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982912 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock119 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 982976 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 19192811 d509 d510
private def d504 : MobiusHarmonicTree := .branch 38354552 d505 d508
private def d496 : MobiusHarmonicTree := .branch 73504179 d497 d504
private def d480 : MobiusHarmonicTree := .branch 128549096 d481 d496
private def d448 : MobiusHarmonicTree := .branch 240637777 d449 d480
private def d384 : MobiusHarmonicTree := .branch 449401833 d385 d448
private def d256 : MobiusHarmonicTree := .branch 672179345 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1036205510 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 966656 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 966656 1036205510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 966656 364026165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 966656 245740419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 966656 138626109 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 966656 61563318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 966656 27370429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 966656 12685319 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966656 5282856 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966784 7402463 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 966912 14685110 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 966912 7072632 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967040 7612478 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 967168 34192889 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 967168 16653713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967168 7894746 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967296 8758967 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 967424 17539176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967424 8330914 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967552 9208262 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 967680 77062791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 967680 40250640 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 967680 19250833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967680 9730940 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967808 9519893 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 967936 20999807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 967936 10607515 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968064 10392292 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 968192 36812151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 968192 19730184 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968192 9821860 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968320 9908324 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 968448 17081967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968448 8736174 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968576 8345793 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 968704 107114310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 968704 72721082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 968704 36939833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 968704 18264334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968704 8711123 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968832 9553211 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 968960 18675499 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 968960 9860500 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969088 8814999 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 969216 35781249 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 969216 20115860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969216 10495475 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969344 9620385 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 969472 15665389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969472 7920355 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969600 7745034 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 969728 34393228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 969728 19838318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 969728 11649518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969728 7301640 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969856 4347878 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 969984 8188800 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 969984 3492690 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 970112 4696110 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 970240 14554910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 970240 7864167 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 970240 3892669 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 970368 3971498 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 970496 6690743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 970496 3740183 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 970624 2950560 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 970752 118285746 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 970752 61636569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 970752 12983498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 970752 8317945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 970752 6145135 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 970752 3340548 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 970880 2804587 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 971008 2172810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971008 831109 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971136 1341701 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 971264 4665553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 971264 764999 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971264 433490 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971392 331509 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 971520 3900554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971520 1055036 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971648 2845518 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 971776 48653071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 971776 22073769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 971776 8210716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971776 3599417 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 971904 4611299 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 972032 13863053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972032 6678421 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972160 7184632 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 972288 26579302 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 972288 14109325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972288 7055118 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972416 7054207 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 972544 12469977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972544 6640977 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972672 5829000 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 972800 56649177 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 972800 30955424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 972800 23049454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 972800 11847846 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972800 5782974 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 972928 6064872 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 973056 11201608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973056 6186373 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973184 5015235 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 973312 7905970 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 973312 6325250 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973312 3859849 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973440 2465401 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 973568 1580720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973568 759107 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973696 821613 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 973824 25693753 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 973824 13498397 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 973824 4474533 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973824 1230175 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 973952 3244358 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 974080 9023864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974080 4308455 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974208 4715409 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 974336 12195356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 974336 6824469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974336 3871163 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974464 2953306 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 974592 5370887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974592 2653298 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974720 2717589 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 974848 672179345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 974848 222777512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 974848 83545209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 974848 44186602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 974848 18110073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 974848 8826014 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974848 4744053 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 974976 4081961 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 975104 9284059 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 975104 4378804 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 975232 4905255 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 975360 26076529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 975360 11233407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 975360 5074770 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 975488 6158637 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 975616 14843122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 975616 7180690 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 975744 7662432 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 975872 39358607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 975872 19797586 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 975872 12236894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 975872 6528172 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976000 5708722 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 976128 7560692 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976128 3912238 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976256 3648454 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 976384 19561021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 976384 8941206 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976384 4890251 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976512 4050955 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 976640 10619815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976640 5050721 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976768 5569094 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 976896 139232303 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 976896 58686893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 976896 23740497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 976896 11451214 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 976896 5619548 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977024 5831666 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 977152 12289283 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977152 5707097 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977280 6582186 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 977408 34946396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 977408 15833784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977408 7744522 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977536 8089262 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 977664 19112612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977664 9738968 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977792 9373644 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 977920 80545410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 977920 36121692 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 977920 18336762 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 977920 9873442 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978048 8463320 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 978176 17784930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978176 8401880 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978304 9383050 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 978432 44423718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 978432 21345690 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978432 10070612 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978560 11275078 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 978688 23078028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978688 11545377 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978816 11532651 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 978944 449401833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 978944 208764056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 978944 88698179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 978944 42544451 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 978944 22037343 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 978944 10964234 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979072 11073109 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 979200 20507108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979200 10537580 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979328 9969528 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 979456 46153728 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 979456 20093246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979456 9312816 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979584 10780430 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 979712 26060482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979712 12797877 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979840 13262605 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 979968 120065877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 979968 59621963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 979968 28416751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 979968 14296518 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980096 14120233 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 980224 31205212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980224 15289437 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980352 15915775 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 980480 60443914 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 980480 30803528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980480 15681172 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980608 15122356 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 980736 29640386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980736 15110176 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980864 14530210 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 980992 240637777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 980992 112088681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 980992 55749776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 980992 28073171 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 980992 14011515 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 981120 14061656 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 981248 27676605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 981248 13875370 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 981376 13801235 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 981504 56338905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 981504 28469046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 981504 14195716 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 981632 14273330 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 981760 27869859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 981760 13465823 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 981888 14404036 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 982016 128549096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 982016 55044917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 982016 26634899 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982016 14275937 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982144 12358962 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 982272 28410018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982272 13419091 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982400 14990927 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 982528 73504179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 982528 35149627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982528 16660086 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982656 18489541 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 982784 38354552 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982784 19161741 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 982912 19192811 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 966656 (MobiusHarmonicTree.branch 1036205510 mobiusHarmonicBlock118 mobiusHarmonicBlock119) = true := Helfgott.combined

#print axioms solution
