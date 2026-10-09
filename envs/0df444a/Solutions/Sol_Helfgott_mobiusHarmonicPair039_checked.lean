-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair039_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:19:28.315952+00:00
-- url     : https://prove2.me/submissions/a6498b76-9886-4b97-bf5c-372f46a1fde3

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638976 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639040 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 784005 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639104 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639168 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 3894146 d11 d12
private def d6 : MobiusHarmonicTree := .branch 4678151 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639232 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639296 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 5366936 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639360 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639424 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 5908490 d18 d19
private def d13 : MobiusHarmonicTree := .branch 11275426 d14 d17
private def d5 : MobiusHarmonicTree := .branch 15953577 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639488 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639552 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 6281056 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639616 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639680 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 6456428 d26 d27
private def d21 : MobiusHarmonicTree := .branch 12737484 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639744 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639808 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 6620750 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639872 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 639936 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 10046353 d33 d34
private def d28 : MobiusHarmonicTree := .branch 16667103 d29 d32
private def d20 : MobiusHarmonicTree := .branch 29404587 d21 d28
private def d4 : MobiusHarmonicTree := .branch 45358164 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640000 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640064 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 9121033 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640128 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640192 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 9195727 d42 d43
private def d37 : MobiusHarmonicTree := .branch 18316760 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640256 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640320 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 8758217 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640384 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640448 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 8013197 d49 d50
private def d44 : MobiusHarmonicTree := .branch 16771414 d45 d48
private def d36 : MobiusHarmonicTree := .branch 35088174 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640512 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640576 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 9255742 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640640 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640704 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 8998027 d57 d58
private def d52 : MobiusHarmonicTree := .branch 18253769 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640768 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640832 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 8824554 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640896 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640960 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 8429580 d64 d65
private def d59 : MobiusHarmonicTree := .branch 17254134 d60 d63
private def d51 : MobiusHarmonicTree := .branch 35507903 d52 d59
private def d35 : MobiusHarmonicTree := .branch 70596077 d36 d51
private def d3 : MobiusHarmonicTree := .branch 115954241 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641024 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641088 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 9597834 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641152 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641216 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 10528495 d74 d75
private def d69 : MobiusHarmonicTree := .branch 20126329 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641280 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641344 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 11145366 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641408 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641472 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 10719201 d81 d82
private def d76 : MobiusHarmonicTree := .branch 21864567 d77 d80
private def d68 : MobiusHarmonicTree := .branch 41990896 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641536 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641600 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 9370378 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641664 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641728 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 9892123 d89 d90
private def d84 : MobiusHarmonicTree := .branch 19262501 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641792 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641856 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 9139194 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641920 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 641984 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 10755757 d96 d97
private def d91 : MobiusHarmonicTree := .branch 19894951 d92 d95
private def d83 : MobiusHarmonicTree := .branch 39157452 d84 d91
private def d67 : MobiusHarmonicTree := .branch 81148348 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642048 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642112 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 12420025 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642176 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642240 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 12440896 d105 d106
private def d100 : MobiusHarmonicTree := .branch 24860921 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642304 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642368 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 13777208 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642432 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642496 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 14527808 d112 d113
private def d107 : MobiusHarmonicTree := .branch 28305016 d108 d111
private def d99 : MobiusHarmonicTree := .branch 53165937 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642560 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642624 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 16581998 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642688 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642752 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 20357826 d120 d121
private def d115 : MobiusHarmonicTree := .branch 36939824 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642816 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642880 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 19810919 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 642944 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643008 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 18085429 d127 d128
private def d122 : MobiusHarmonicTree := .branch 37896348 d123 d126
private def d114 : MobiusHarmonicTree := .branch 74836172 d115 d122
private def d98 : MobiusHarmonicTree := .branch 128002109 d99 d114
private def d66 : MobiusHarmonicTree := .branch 209150457 d67 d98
private def d2 : MobiusHarmonicTree := .branch 325104698 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643072 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643136 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 18406716 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643200 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643264 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 17548101 d138 d139
private def d133 : MobiusHarmonicTree := .branch 35954817 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643328 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643392 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 18034161 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643456 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643520 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 18760942 d145 d146
private def d140 : MobiusHarmonicTree := .branch 36795103 d141 d144
private def d132 : MobiusHarmonicTree := .branch 72749920 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643584 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643648 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 20439771 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643712 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643776 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 20435753 d153 d154
private def d148 : MobiusHarmonicTree := .branch 40875524 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643840 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643904 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 19681610 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 643968 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644032 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 18921529 d160 d161
private def d155 : MobiusHarmonicTree := .branch 38603139 d156 d159
private def d147 : MobiusHarmonicTree := .branch 79478663 d148 d155
private def d131 : MobiusHarmonicTree := .branch 152228583 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644096 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644160 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 17820200 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644224 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644288 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 18262086 d169 d170
private def d164 : MobiusHarmonicTree := .branch 36082286 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644352 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644416 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 17985345 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644480 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644544 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 17347258 d176 d177
private def d171 : MobiusHarmonicTree := .branch 35332603 d172 d175
private def d163 : MobiusHarmonicTree := .branch 71414889 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644608 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644672 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 17533014 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644736 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644800 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 18205728 d184 d185
private def d179 : MobiusHarmonicTree := .branch 35738742 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644864 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644928 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 16761649 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 644992 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645056 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 15271636 d191 d192
private def d186 : MobiusHarmonicTree := .branch 32033285 d187 d190
private def d178 : MobiusHarmonicTree := .branch 67772027 d179 d186
private def d162 : MobiusHarmonicTree := .branch 139186916 d163 d178
private def d130 : MobiusHarmonicTree := .branch 291415499 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645120 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645184 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 16730141 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645248 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645312 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 20021390 d201 d202
private def d196 : MobiusHarmonicTree := .branch 36751531 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645376 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645440 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 19803614 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645504 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645568 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 20967640 d208 d209
private def d203 : MobiusHarmonicTree := .branch 40771254 d204 d207
private def d195 : MobiusHarmonicTree := .branch 77522785 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645632 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645696 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 20142691 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645760 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645824 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 21462569 d216 d217
private def d211 : MobiusHarmonicTree := .branch 41605260 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645888 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 645952 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 22136379 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646016 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646080 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 22433836 d223 d224
private def d218 : MobiusHarmonicTree := .branch 44570215 d219 d222
private def d210 : MobiusHarmonicTree := .branch 86175475 d211 d218
private def d194 : MobiusHarmonicTree := .branch 163698260 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646144 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646208 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 22489721 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646272 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646336 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 20801978 d232 d233
private def d227 : MobiusHarmonicTree := .branch 43291699 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646400 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646464 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 20958656 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646528 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646592 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 20456627 d239 d240
private def d234 : MobiusHarmonicTree := .branch 41415283 d235 d238
private def d226 : MobiusHarmonicTree := .branch 84706982 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646656 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646720 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 19905094 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646784 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646848 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 20391268 d247 d248
private def d242 : MobiusHarmonicTree := .branch 40296362 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646912 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 646976 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 18492311 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647040 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock078 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647104 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 16535315 d254 d255
private def d249 : MobiusHarmonicTree := .branch 35027626 d250 d253
private def d241 : MobiusHarmonicTree := .branch 75323988 d242 d249
private def d225 : MobiusHarmonicTree := .branch 160030970 d226 d241
private def d193 : MobiusHarmonicTree := .branch 323729230 d194 d225
private def d129 : MobiusHarmonicTree := .branch 615144729 d130 d193
private def d1 : MobiusHarmonicTree := .branch 940249427 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647168 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647232 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 16675683 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647296 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647360 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 17846416 d266 d267
private def d261 : MobiusHarmonicTree := .branch 34522099 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647424 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647488 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 19084593 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647552 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647616 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 17978382 d273 d274
private def d268 : MobiusHarmonicTree := .branch 37062975 d269 d272
private def d260 : MobiusHarmonicTree := .branch 71585074 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647680 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647744 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 16310557 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647808 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647872 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 16578960 d281 d282
private def d276 : MobiusHarmonicTree := .branch 32889517 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 647936 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648000 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 18001637 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648064 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648128 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 17117029 d288 d289
private def d283 : MobiusHarmonicTree := .branch 35118666 d284 d287
private def d275 : MobiusHarmonicTree := .branch 68008183 d276 d283
private def d259 : MobiusHarmonicTree := .branch 139593257 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648192 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648256 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 18909309 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648320 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648384 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 17617721 d297 d298
private def d292 : MobiusHarmonicTree := .branch 36527030 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648448 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648512 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 19586408 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648576 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648640 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 21281487 d304 d305
private def d299 : MobiusHarmonicTree := .branch 40867895 d300 d303
private def d291 : MobiusHarmonicTree := .branch 77394925 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648704 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648768 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 22368623 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648832 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648896 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 23150178 d312 d313
private def d307 : MobiusHarmonicTree := .branch 45518801 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 648960 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649024 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 24279572 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649088 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649152 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 25191367 d319 d320
private def d314 : MobiusHarmonicTree := .branch 49470939 d315 d318
private def d306 : MobiusHarmonicTree := .branch 94989740 d307 d314
private def d290 : MobiusHarmonicTree := .branch 172384665 d291 d306
private def d258 : MobiusHarmonicTree := .branch 311977922 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649216 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649280 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 27165536 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649344 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649408 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 28341276 d329 d330
private def d324 : MobiusHarmonicTree := .branch 55506812 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649472 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649536 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 28275689 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649600 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649664 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 24966888 d336 d337
private def d331 : MobiusHarmonicTree := .branch 53242577 d332 d335
private def d323 : MobiusHarmonicTree := .branch 108749389 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649728 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649792 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 23184463 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649856 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649920 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 24370736 d344 d345
private def d339 : MobiusHarmonicTree := .branch 47555199 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 649984 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650048 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 27602624 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650112 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650176 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 27952511 d351 d352
private def d346 : MobiusHarmonicTree := .branch 55555135 d347 d350
private def d338 : MobiusHarmonicTree := .branch 103110334 d339 d346
private def d322 : MobiusHarmonicTree := .branch 211859723 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650240 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650304 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 27550276 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650368 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650432 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 29262134 d360 d361
private def d355 : MobiusHarmonicTree := .branch 56812410 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650496 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650560 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 31374607 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650624 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650688 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 30729091 d367 d368
private def d362 : MobiusHarmonicTree := .branch 62103698 d363 d366
private def d354 : MobiusHarmonicTree := .branch 118916108 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650752 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650816 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 29046745 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650880 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 650944 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 28214504 d375 d376
private def d370 : MobiusHarmonicTree := .branch 57261249 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651008 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651072 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 28373307 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651136 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651200 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 27168406 d382 d383
private def d377 : MobiusHarmonicTree := .branch 55541713 d378 d381
private def d369 : MobiusHarmonicTree := .branch 112802962 d370 d377
private def d353 : MobiusHarmonicTree := .branch 231719070 d354 d369
private def d321 : MobiusHarmonicTree := .branch 443578793 d322 d353
private def d257 : MobiusHarmonicTree := .branch 755556715 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651264 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651328 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 27000261 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651392 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651456 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 29048877 d393 d394
private def d388 : MobiusHarmonicTree := .branch 56049138 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651520 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651584 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 29851890 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651648 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651712 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 32179921 d400 d401
private def d395 : MobiusHarmonicTree := .branch 62031811 d396 d399
private def d387 : MobiusHarmonicTree := .branch 118080949 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651776 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651840 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 31641351 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651904 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 651968 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 31469375 d408 d409
private def d403 : MobiusHarmonicTree := .branch 63110726 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652032 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652096 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 35504009 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652160 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652224 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 37507165 d415 d416
private def d410 : MobiusHarmonicTree := .branch 73011174 d411 d414
private def d402 : MobiusHarmonicTree := .branch 136121900 d403 d410
private def d386 : MobiusHarmonicTree := .branch 254202849 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652288 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652352 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 36445143 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652416 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652480 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 36643386 d424 d425
private def d419 : MobiusHarmonicTree := .branch 73088529 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652544 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652608 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 33596127 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652672 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652736 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 33275403 d431 d432
private def d426 : MobiusHarmonicTree := .branch 66871530 d427 d430
private def d418 : MobiusHarmonicTree := .branch 139960059 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652800 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652864 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 32190582 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652928 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 652992 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 29416990 d439 d440
private def d434 : MobiusHarmonicTree := .branch 61607572 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653056 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653120 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 30042029 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653184 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653248 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 31167397 d446 d447
private def d441 : MobiusHarmonicTree := .branch 61209426 d442 d445
private def d433 : MobiusHarmonicTree := .branch 122816998 d434 d441
private def d417 : MobiusHarmonicTree := .branch 262777057 d418 d433
private def d385 : MobiusHarmonicTree := .branch 516979906 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653312 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653376 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 33854953 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653440 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653504 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 34491122 d456 d457
private def d451 : MobiusHarmonicTree := .branch 68346075 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653568 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653632 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 31501034 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653696 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653760 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 29772522 d463 d464
private def d458 : MobiusHarmonicTree := .branch 61273556 d459 d462
private def d450 : MobiusHarmonicTree := .branch 129619631 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653824 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653888 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 28407083 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 653952 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654016 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 27123301 d471 d472
private def d466 : MobiusHarmonicTree := .branch 55530384 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654080 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654144 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 26998724 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654208 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654272 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 26956740 d478 d479
private def d473 : MobiusHarmonicTree := .branch 53955464 d474 d477
private def d465 : MobiusHarmonicTree := .branch 109485848 d466 d473
private def d449 : MobiusHarmonicTree := .branch 239105479 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654336 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654400 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 29280289 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654464 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654528 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 30142479 d487 d488
private def d482 : MobiusHarmonicTree := .branch 59422768 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654592 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654656 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 28531086 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654720 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654784 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 26598214 d494 d495
private def d489 : MobiusHarmonicTree := .branch 55129300 d490 d493
private def d481 : MobiusHarmonicTree := .branch 114552068 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654848 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654912 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 25983707 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 654976 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 655040 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 26351157 d502 d503
private def d497 : MobiusHarmonicTree := .branch 52334864 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 655104 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 655168 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 27869238 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 655232 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock079 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 655296 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 28651281 d509 d510
private def d504 : MobiusHarmonicTree := .branch 56520519 d505 d508
private def d496 : MobiusHarmonicTree := .branch 108855383 d497 d504
private def d480 : MobiusHarmonicTree := .branch 223407451 d481 d496
private def d448 : MobiusHarmonicTree := .branch 462512930 d449 d480
private def d384 : MobiusHarmonicTree := .branch 979492836 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1735049551 d257 d384
private def d0 : MobiusHarmonicTree := .branch 2675298978 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 638976 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 638976 2675298978 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 638976 940249427 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 638976 325104698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 638976 115954241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 638976 45358164 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 638976 15953577 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 638976 4678151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638976 784005 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 639104 3894146 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 639232 11275426 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 639232 5366936 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 639360 5908490 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 639488 29404587 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 639488 12737484 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 639488 6281056 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 639616 6456428 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 639744 16667103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 639744 6620750 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 639872 10046353 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 640000 70596077 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 640000 35088174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 640000 18316760 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640000 9121033 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640128 9195727 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 640256 16771414 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640256 8758217 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640384 8013197 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 640512 35507903 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 640512 18253769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640512 9255742 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640640 8998027 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 640768 17254134 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640768 8824554 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640896 8429580 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 641024 209150457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 641024 81148348 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 641024 41990896 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 641024 20126329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641024 9597834 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641152 10528495 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 641280 21864567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641280 11145366 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641408 10719201 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 641536 39157452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 641536 19262501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641536 9370378 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641664 9892123 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 641792 19894951 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641792 9139194 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 641920 10755757 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 642048 128002109 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 642048 53165937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 642048 24860921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642048 12420025 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642176 12440896 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 642304 28305016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642304 13777208 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642432 14527808 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 642560 74836172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 642560 36939824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642560 16581998 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642688 20357826 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 642816 37896348 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642816 19810919 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 642944 18085429 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 643072 615144729 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 643072 291415499 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 643072 152228583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 643072 72749920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 643072 35954817 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643072 18406716 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643200 17548101 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 643328 36795103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643328 18034161 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643456 18760942 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 643584 79478663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 643584 40875524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643584 20439771 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643712 20435753 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 643840 38603139 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643840 19681610 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 643968 18921529 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 644096 139186916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 644096 71414889 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 644096 36082286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644096 17820200 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644224 18262086 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 644352 35332603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644352 17985345 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644480 17347258 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 644608 67772027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 644608 35738742 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644608 17533014 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644736 18205728 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 644864 32033285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644864 16761649 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 644992 15271636 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 645120 323729230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 645120 163698260 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 645120 77522785 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 645120 36751531 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 645120 16730141 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 645248 20021390 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 645376 40771254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 645376 19803614 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 645504 20967640 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 645632 86175475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 645632 41605260 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 645632 20142691 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 645760 21462569 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 645888 44570215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 645888 22136379 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646016 22433836 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 646144 160030970 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 646144 84706982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 646144 43291699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646144 22489721 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646272 20801978 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 646400 41415283 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646400 20958656 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646528 20456627 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 646656 75323988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 646656 40296362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646656 19905094 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646784 20391268 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 646912 35027626 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 646912 18492311 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647040 16535315 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 647168 1735049551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 647168 755556715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 647168 311977922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 647168 139593257 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 647168 71585074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 647168 34522099 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647168 16675683 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647296 17846416 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 647424 37062975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647424 19084593 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647552 17978382 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 647680 68008183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 647680 32889517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647680 16310557 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647808 16578960 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 647936 35118666 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 647936 18001637 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648064 17117029 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 648192 172384665 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 648192 77394925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 648192 36527030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648192 18909309 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648320 17617721 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 648448 40867895 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648448 19586408 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648576 21281487 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 648704 94989740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 648704 45518801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648704 22368623 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648832 23150178 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 648960 49470939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 648960 24279572 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649088 25191367 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 649216 443578793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 649216 211859723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 649216 108749389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 649216 55506812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649216 27165536 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649344 28341276 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 649472 53242577 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649472 28275689 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649600 24966888 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 649728 103110334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 649728 47555199 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649728 23184463 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649856 24370736 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 649984 55555135 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 649984 27602624 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 650112 27952511 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 650240 231719070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 650240 118916108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 650240 56812410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 650240 27550276 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 650368 29262134 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 650496 62103698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 650496 31374607 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 650624 30729091 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 650752 112802962 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 650752 57261249 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 650752 29046745 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 650880 28214504 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 651008 55541713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651008 28373307 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651136 27168406 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 651264 979492836 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 651264 516979906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 651264 254202849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 651264 118080949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 651264 56049138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651264 27000261 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651392 29048877 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 651520 62031811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651520 29851890 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651648 32179921 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 651776 136121900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 651776 63110726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651776 31641351 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 651904 31469375 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 652032 73011174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652032 35504009 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652160 37507165 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 652288 262777057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 652288 139960059 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 652288 73088529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652288 36445143 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652416 36643386 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 652544 66871530 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652544 33596127 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652672 33275403 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 652800 122816998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 652800 61607572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652800 32190582 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 652928 29416990 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 653056 61209426 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653056 30042029 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653184 31167397 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 653312 462512930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 653312 239105479 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 653312 129619631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 653312 68346075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653312 33854953 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653440 34491122 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 653568 61273556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653568 31501034 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653696 29772522 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 653824 109485848 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 653824 55530384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653824 28407083 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 653952 27123301 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 654080 53955464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654080 26998724 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654208 26956740 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 654336 223407451 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 654336 114552068 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 654336 59422768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654336 29280289 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654464 30142479 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 654592 55129300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654592 28531086 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654720 26598214 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 654848 108855383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 654848 52334864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654848 25983707 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 654976 26351157 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 655104 56520519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 655104 27869238 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 655232 28651281 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 638976 (MobiusHarmonicTree.branch 2675298978 mobiusHarmonicBlock078 mobiusHarmonicBlock079) = true := Helfgott.combined

#print axioms solution
