-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair055_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:18:49.083814+00:00
-- url     : https://prove2.me/submissions/f454730b-72e9-40ae-ae3e-39c489e46e68

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901120 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901184 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 32994443 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901248 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901312 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 31616228 d11 d12
private def d6 : MobiusHarmonicTree := .branch 64610671 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901376 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901440 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 31712663 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901504 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901568 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 32573334 d18 d19
private def d13 : MobiusHarmonicTree := .branch 64285997 d14 d17
private def d5 : MobiusHarmonicTree := .branch 128896668 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901632 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901696 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 31285598 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901760 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901824 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 29125503 d26 d27
private def d21 : MobiusHarmonicTree := .branch 60411101 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901888 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 901952 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 29136885 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902016 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902080 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 30239083 d33 d34
private def d28 : MobiusHarmonicTree := .branch 59375968 d29 d32
private def d20 : MobiusHarmonicTree := .branch 119787069 d21 d28
private def d4 : MobiusHarmonicTree := .branch 248683737 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902144 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902208 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 29294890 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902272 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902336 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 30382319 d42 d43
private def d37 : MobiusHarmonicTree := .branch 59677209 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902400 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902464 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 30974166 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902528 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902592 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 29997045 d49 d50
private def d44 : MobiusHarmonicTree := .branch 60971211 d45 d48
private def d36 : MobiusHarmonicTree := .branch 120648420 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902656 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902720 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 27854803 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902784 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902848 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 27727895 d57 d58
private def d52 : MobiusHarmonicTree := .branch 55582698 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902912 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 902976 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 27699592 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903040 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903104 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 27350211 d64 d65
private def d59 : MobiusHarmonicTree := .branch 55049803 d60 d63
private def d51 : MobiusHarmonicTree := .branch 110632501 d52 d59
private def d35 : MobiusHarmonicTree := .branch 231280921 d36 d51
private def d3 : MobiusHarmonicTree := .branch 479964658 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903168 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903232 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 25729913 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903296 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903360 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 24261740 d74 d75
private def d69 : MobiusHarmonicTree := .branch 49991653 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903424 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903488 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 24229499 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903552 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903616 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 23605256 d81 d82
private def d76 : MobiusHarmonicTree := .branch 47834755 d77 d80
private def d68 : MobiusHarmonicTree := .branch 97826408 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903680 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903744 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 22949066 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903808 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903872 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 21489855 d89 d90
private def d84 : MobiusHarmonicTree := .branch 44438921 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 903936 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904000 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 20939264 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904064 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904128 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 20612186 d96 d97
private def d91 : MobiusHarmonicTree := .branch 41551450 d92 d95
private def d83 : MobiusHarmonicTree := .branch 85990371 d84 d91
private def d67 : MobiusHarmonicTree := .branch 183816779 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904192 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904256 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 20210088 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904320 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904384 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 19439837 d105 d106
private def d100 : MobiusHarmonicTree := .branch 39649925 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904448 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904512 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 18377949 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904576 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904640 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 19435411 d112 d113
private def d107 : MobiusHarmonicTree := .branch 37813360 d108 d111
private def d99 : MobiusHarmonicTree := .branch 77463285 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904704 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904768 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 21679630 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904832 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904896 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 22955185 d120 d121
private def d115 : MobiusHarmonicTree := .branch 44634815 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 904960 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905024 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 23158586 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905088 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905152 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 22578588 d127 d128
private def d122 : MobiusHarmonicTree := .branch 45737174 d123 d126
private def d114 : MobiusHarmonicTree := .branch 90371989 d115 d122
private def d98 : MobiusHarmonicTree := .branch 167835274 d99 d114
private def d66 : MobiusHarmonicTree := .branch 351652053 d67 d98
private def d2 : MobiusHarmonicTree := .branch 831616711 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905216 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905280 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 24121881 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905344 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905408 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 24590119 d138 d139
private def d133 : MobiusHarmonicTree := .branch 48712000 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905472 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905536 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 24486134 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905600 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905664 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 24340227 d145 d146
private def d140 : MobiusHarmonicTree := .branch 48826361 d141 d144
private def d132 : MobiusHarmonicTree := .branch 97538361 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905728 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905792 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 24793840 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905856 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905920 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 24279274 d153 d154
private def d148 : MobiusHarmonicTree := .branch 49073114 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 905984 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906048 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 24879532 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906112 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906176 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 25132059 d160 d161
private def d155 : MobiusHarmonicTree := .branch 50011591 d156 d159
private def d147 : MobiusHarmonicTree := .branch 99084705 d148 d155
private def d131 : MobiusHarmonicTree := .branch 196623066 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906240 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906304 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 24699291 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906368 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906432 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 25358833 d169 d170
private def d164 : MobiusHarmonicTree := .branch 50058124 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906496 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906560 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 24930606 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906624 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906688 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 24665658 d176 d177
private def d171 : MobiusHarmonicTree := .branch 49596264 d172 d175
private def d163 : MobiusHarmonicTree := .branch 99654388 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906752 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906816 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 24903681 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906880 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 906944 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 26129556 d184 d185
private def d179 : MobiusHarmonicTree := .branch 51033237 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907008 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907072 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 28114697 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907136 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907200 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 29006914 d191 d192
private def d186 : MobiusHarmonicTree := .branch 57121611 d187 d190
private def d178 : MobiusHarmonicTree := .branch 108154848 d179 d186
private def d162 : MobiusHarmonicTree := .branch 207809236 d163 d178
private def d130 : MobiusHarmonicTree := .branch 404432302 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907264 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907328 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 29599063 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907392 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907456 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 31221420 d201 d202
private def d196 : MobiusHarmonicTree := .branch 60820483 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907520 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907584 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 30547132 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907648 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907712 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 30751015 d208 d209
private def d203 : MobiusHarmonicTree := .branch 61298147 d204 d207
private def d195 : MobiusHarmonicTree := .branch 122118630 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907776 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907840 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 29885312 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907904 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 907968 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 30020954 d216 d217
private def d211 : MobiusHarmonicTree := .branch 59906266 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908032 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908096 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 29283344 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908160 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908224 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 28512865 d223 d224
private def d218 : MobiusHarmonicTree := .branch 57796209 d219 d222
private def d210 : MobiusHarmonicTree := .branch 117702475 d211 d218
private def d194 : MobiusHarmonicTree := .branch 239821105 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908288 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908352 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 28698199 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908416 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908480 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 29925875 d232 d233
private def d227 : MobiusHarmonicTree := .branch 58624074 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908544 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908608 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 31236872 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908672 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908736 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 30221200 d239 d240
private def d234 : MobiusHarmonicTree := .branch 61458072 d235 d238
private def d226 : MobiusHarmonicTree := .branch 120082146 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908800 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908864 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 30113470 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908928 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 908992 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 31680221 d247 d248
private def d242 : MobiusHarmonicTree := .branch 61793691 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909056 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909120 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 32450125 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909184 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock110 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909248 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 32631461 d254 d255
private def d249 : MobiusHarmonicTree := .branch 65081586 d250 d253
private def d241 : MobiusHarmonicTree := .branch 126875277 d242 d249
private def d225 : MobiusHarmonicTree := .branch 246957423 d226 d241
private def d193 : MobiusHarmonicTree := .branch 486778528 d194 d225
private def d129 : MobiusHarmonicTree := .branch 891210830 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1722827541 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909312 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909376 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 34878923 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909440 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909504 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 35403980 d266 d267
private def d261 : MobiusHarmonicTree := .branch 70282903 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909568 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909632 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 36143257 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909696 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909760 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 37490162 d273 d274
private def d268 : MobiusHarmonicTree := .branch 73633419 d269 d272
private def d260 : MobiusHarmonicTree := .branch 143916322 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909824 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909888 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 38221281 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 909952 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910016 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 37608218 d281 d282
private def d276 : MobiusHarmonicTree := .branch 75829499 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910080 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910144 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 38184143 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910208 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910272 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 38631415 d288 d289
private def d283 : MobiusHarmonicTree := .branch 76815558 d284 d287
private def d275 : MobiusHarmonicTree := .branch 152645057 d276 d283
private def d259 : MobiusHarmonicTree := .branch 296561379 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910336 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910400 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 37219983 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910464 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910528 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 36445995 d297 d298
private def d292 : MobiusHarmonicTree := .branch 73665978 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910592 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910656 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 34738810 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910720 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910784 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 33271424 d304 d305
private def d299 : MobiusHarmonicTree := .branch 68010234 d300 d303
private def d291 : MobiusHarmonicTree := .branch 141676212 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910848 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910912 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 32452191 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 910976 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911040 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 31015199 d312 d313
private def d307 : MobiusHarmonicTree := .branch 63467390 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911104 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911168 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 30589397 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911232 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911296 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 31262135 d319 d320
private def d314 : MobiusHarmonicTree := .branch 61851532 d315 d318
private def d306 : MobiusHarmonicTree := .branch 125318922 d307 d314
private def d290 : MobiusHarmonicTree := .branch 266995134 d291 d306
private def d258 : MobiusHarmonicTree := .branch 563556513 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911360 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911424 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 32015912 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911488 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911552 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 31708638 d329 d330
private def d324 : MobiusHarmonicTree := .branch 63724550 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911616 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911680 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 32848209 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911744 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911808 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 33409537 d336 d337
private def d331 : MobiusHarmonicTree := .branch 66257746 d332 d335
private def d323 : MobiusHarmonicTree := .branch 129982296 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911872 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 911936 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 32537458 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912000 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912064 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 31393721 d344 d345
private def d339 : MobiusHarmonicTree := .branch 63931179 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912128 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912192 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 30814846 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912256 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912320 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 32122574 d351 d352
private def d346 : MobiusHarmonicTree := .branch 62937420 d347 d350
private def d338 : MobiusHarmonicTree := .branch 126868599 d339 d346
private def d322 : MobiusHarmonicTree := .branch 256850895 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912384 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912448 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 32380000 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912512 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912576 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 33177597 d360 d361
private def d355 : MobiusHarmonicTree := .branch 65557597 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912640 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912704 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 32825630 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912768 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912832 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 31966524 d367 d368
private def d362 : MobiusHarmonicTree := .branch 64792154 d363 d366
private def d354 : MobiusHarmonicTree := .branch 130349751 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912896 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 912960 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 31185468 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913024 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913088 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 28684108 d375 d376
private def d370 : MobiusHarmonicTree := .branch 59869576 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913152 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913216 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 27019985 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913280 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913344 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 26915447 d382 d383
private def d377 : MobiusHarmonicTree := .branch 53935432 d378 d381
private def d369 : MobiusHarmonicTree := .branch 113805008 d370 d377
private def d353 : MobiusHarmonicTree := .branch 244154759 d354 d369
private def d321 : MobiusHarmonicTree := .branch 501005654 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1064562167 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913408 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913472 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 26940162 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913536 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913600 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 24696887 d393 d394
private def d388 : MobiusHarmonicTree := .branch 51637049 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913664 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913728 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 24952782 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913792 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913856 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 25968052 d400 d401
private def d395 : MobiusHarmonicTree := .branch 50920834 d396 d399
private def d387 : MobiusHarmonicTree := .branch 102557883 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913920 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 913984 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 27520243 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914048 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914112 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 27016487 d408 d409
private def d403 : MobiusHarmonicTree := .branch 54536730 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914176 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914240 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 26347638 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914304 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914368 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 27681475 d415 d416
private def d410 : MobiusHarmonicTree := .branch 54029113 d411 d414
private def d402 : MobiusHarmonicTree := .branch 108565843 d403 d410
private def d386 : MobiusHarmonicTree := .branch 211123726 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914432 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914496 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 26785346 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914560 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914624 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 26710500 d424 d425
private def d419 : MobiusHarmonicTree := .branch 53495846 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914688 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914752 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 26790954 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914816 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914880 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 26634165 d431 d432
private def d426 : MobiusHarmonicTree := .branch 53425119 d427 d430
private def d418 : MobiusHarmonicTree := .branch 106920965 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 914944 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915008 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 27403109 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915072 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915136 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 27515131 d439 d440
private def d434 : MobiusHarmonicTree := .branch 54918240 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915200 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915264 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 27671870 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915328 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915392 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 26842146 d446 d447
private def d441 : MobiusHarmonicTree := .branch 54514016 d442 d445
private def d433 : MobiusHarmonicTree := .branch 109432256 d434 d441
private def d417 : MobiusHarmonicTree := .branch 216353221 d418 d433
private def d385 : MobiusHarmonicTree := .branch 427476947 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915456 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915520 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 26482286 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915584 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915648 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 27860120 d456 d457
private def d451 : MobiusHarmonicTree := .branch 54342406 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915712 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915776 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 28964566 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915840 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915904 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 30416998 d463 d464
private def d458 : MobiusHarmonicTree := .branch 59381564 d459 d462
private def d450 : MobiusHarmonicTree := .branch 113723970 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 915968 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916032 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 30006697 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916096 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916160 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 30058123 d471 d472
private def d466 : MobiusHarmonicTree := .branch 60064820 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916224 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916288 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 30080136 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916352 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916416 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 30580085 d478 d479
private def d473 : MobiusHarmonicTree := .branch 60660221 d474 d477
private def d465 : MobiusHarmonicTree := .branch 120725041 d466 d473
private def d449 : MobiusHarmonicTree := .branch 234449011 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916480 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916544 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 29731337 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916608 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916672 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 29399920 d487 d488
private def d482 : MobiusHarmonicTree := .branch 59131257 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916736 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916800 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 27993123 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916864 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916928 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 27485347 d494 d495
private def d489 : MobiusHarmonicTree := .branch 55478470 d490 d493
private def d481 : MobiusHarmonicTree := .branch 114609727 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 916992 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917056 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 27376793 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917120 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917184 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 28166746 d502 d503
private def d497 : MobiusHarmonicTree := .branch 55543539 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917248 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917312 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 27435673 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917376 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock111 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917440 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 27093958 d509 d510
private def d504 : MobiusHarmonicTree := .branch 54529631 d505 d508
private def d496 : MobiusHarmonicTree := .branch 110073170 d497 d504
private def d480 : MobiusHarmonicTree := .branch 224682897 d481 d496
private def d448 : MobiusHarmonicTree := .branch 459131908 d449 d480
private def d384 : MobiusHarmonicTree := .branch 886608855 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1951171022 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3673998563 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 901120 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 901120 3673998563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 901120 1722827541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 901120 831616711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 901120 479964658 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 901120 248683737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 901120 128896668 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 901120 64610671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 901120 32994443 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 901248 31616228 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 901376 64285997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 901376 31712663 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 901504 32573334 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 901632 119787069 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 901632 60411101 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 901632 31285598 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 901760 29125503 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 901888 59375968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 901888 29136885 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902016 30239083 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 902144 231280921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 902144 120648420 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 902144 59677209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902144 29294890 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902272 30382319 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 902400 60971211 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902400 30974166 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902528 29997045 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 902656 110632501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 902656 55582698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902656 27854803 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902784 27727895 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 902912 55049803 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 902912 27699592 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903040 27350211 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 903168 351652053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 903168 183816779 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 903168 97826408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 903168 49991653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903168 25729913 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903296 24261740 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 903424 47834755 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903424 24229499 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903552 23605256 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 903680 85990371 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 903680 44438921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903680 22949066 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903808 21489855 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 903936 41551450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 903936 20939264 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904064 20612186 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 904192 167835274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 904192 77463285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 904192 39649925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904192 20210088 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904320 19439837 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 904448 37813360 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904448 18377949 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904576 19435411 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 904704 90371989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 904704 44634815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904704 21679630 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904832 22955185 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 904960 45737174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 904960 23158586 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905088 22578588 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 905216 891210830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 905216 404432302 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 905216 196623066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 905216 97538361 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 905216 48712000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905216 24121881 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905344 24590119 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 905472 48826361 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905472 24486134 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905600 24340227 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 905728 99084705 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 905728 49073114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905728 24793840 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905856 24279274 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 905984 50011591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 905984 24879532 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 906112 25132059 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 906240 207809236 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 906240 99654388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 906240 50058124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 906240 24699291 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 906368 25358833 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 906496 49596264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 906496 24930606 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 906624 24665658 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 906752 108154848 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 906752 51033237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 906752 24903681 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 906880 26129556 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 907008 57121611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907008 28114697 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907136 29006914 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 907264 486778528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 907264 239821105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 907264 122118630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 907264 60820483 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907264 29599063 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907392 31221420 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 907520 61298147 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907520 30547132 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907648 30751015 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 907776 117702475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 907776 59906266 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907776 29885312 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 907904 30020954 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 908032 57796209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908032 29283344 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908160 28512865 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 908288 246957423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 908288 120082146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 908288 58624074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908288 28698199 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908416 29925875 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 908544 61458072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908544 31236872 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908672 30221200 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 908800 126875277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 908800 61793691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908800 30113470 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 908928 31680221 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 909056 65081586 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909056 32450125 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909184 32631461 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 909312 1951171022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 909312 1064562167 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 909312 563556513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 909312 296561379 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 909312 143916322 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 909312 70282903 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909312 34878923 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909440 35403980 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 909568 73633419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909568 36143257 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909696 37490162 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 909824 152645057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 909824 75829499 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909824 38221281 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 909952 37608218 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 910080 76815558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910080 38184143 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910208 38631415 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 910336 266995134 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 910336 141676212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 910336 73665978 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910336 37219983 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910464 36445995 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 910592 68010234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910592 34738810 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910720 33271424 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 910848 125318922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 910848 63467390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910848 32452191 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 910976 31015199 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 911104 61851532 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 911104 30589397 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 911232 31262135 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 911360 501005654 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 911360 256850895 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 911360 129982296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 911360 63724550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 911360 32015912 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 911488 31708638 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 911616 66257746 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 911616 32848209 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 911744 33409537 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 911872 126868599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 911872 63931179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 911872 32537458 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912000 31393721 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 912128 62937420 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912128 30814846 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912256 32122574 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 912384 244154759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 912384 130349751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 912384 65557597 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912384 32380000 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912512 33177597 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 912640 64792154 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912640 32825630 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912768 31966524 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 912896 113805008 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 912896 59869576 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 912896 31185468 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913024 28684108 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 913152 53935432 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913152 27019985 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913280 26915447 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 913408 886608855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 913408 427476947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 913408 211123726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 913408 102557883 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 913408 51637049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913408 26940162 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913536 24696887 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 913664 50920834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913664 24952782 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913792 25968052 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 913920 108565843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 913920 54536730 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 913920 27520243 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914048 27016487 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 914176 54029113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914176 26347638 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914304 27681475 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 914432 216353221 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 914432 106920965 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 914432 53495846 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914432 26785346 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914560 26710500 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 914688 53425119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914688 26790954 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914816 26634165 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 914944 109432256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 914944 54918240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 914944 27403109 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915072 27515131 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 915200 54514016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915200 27671870 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915328 26842146 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 915456 459131908 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 915456 234449011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 915456 113723970 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 915456 54342406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915456 26482286 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915584 27860120 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 915712 59381564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915712 28964566 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915840 30416998 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 915968 120725041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 915968 60064820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 915968 30006697 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916096 30058123 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 916224 60660221 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916224 30080136 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916352 30580085 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 916480 224682897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 916480 114609727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 916480 59131257 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916480 29731337 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916608 29399920 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 916736 55478470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916736 27993123 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916864 27485347 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 916992 110073170 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 916992 55543539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 916992 27376793 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 917120 28166746 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 917248 54529631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 917248 27435673 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 917376 27093958 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 901120 (MobiusHarmonicTree.branch 3673998563 mobiusHarmonicBlock110 mobiusHarmonicBlock111) = true := Helfgott.combined

#print axioms solution
