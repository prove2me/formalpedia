-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair038_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:16:17.299476+00:00
-- url     : https://prove2.me/submissions/aa6dc652-b199-4f7b-9a96-1496d81c6fca

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622592 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622656 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 34426830 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622720 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622784 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 32658299 d11 d12
private def d6 : MobiusHarmonicTree := .branch 67085129 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622848 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622912 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 32319266 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622976 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623040 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 33575755 d18 d19
private def d13 : MobiusHarmonicTree := .branch 65895021 d14 d17
private def d5 : MobiusHarmonicTree := .branch 132980150 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623104 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623168 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 31290245 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623232 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623296 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 32166165 d26 d27
private def d21 : MobiusHarmonicTree := .branch 63456410 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623360 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623424 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 31514787 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623488 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623552 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 28068364 d33 d34
private def d28 : MobiusHarmonicTree := .branch 59583151 d29 d32
private def d20 : MobiusHarmonicTree := .branch 123039561 d21 d28
private def d4 : MobiusHarmonicTree := .branch 256019711 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623616 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623680 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 28158703 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623744 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623808 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 30007699 d42 d43
private def d37 : MobiusHarmonicTree := .branch 58166402 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623872 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 623936 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 30185870 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624000 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624064 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 31964714 d49 d50
private def d44 : MobiusHarmonicTree := .branch 62150584 d45 d48
private def d36 : MobiusHarmonicTree := .branch 120316986 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624128 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624192 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 34140185 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624256 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624320 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 36760061 d57 d58
private def d52 : MobiusHarmonicTree := .branch 70900246 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624384 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624448 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 36818229 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624512 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624576 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 36498464 d64 d65
private def d59 : MobiusHarmonicTree := .branch 73316693 d60 d63
private def d51 : MobiusHarmonicTree := .branch 144216939 d52 d59
private def d35 : MobiusHarmonicTree := .branch 264533925 d36 d51
private def d3 : MobiusHarmonicTree := .branch 520553636 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624640 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624704 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 35745005 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624768 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624832 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 35220746 d74 d75
private def d69 : MobiusHarmonicTree := .branch 70965751 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624896 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 624960 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 35787944 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625024 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625088 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 37321225 d81 d82
private def d76 : MobiusHarmonicTree := .branch 73109169 d77 d80
private def d68 : MobiusHarmonicTree := .branch 144074920 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625152 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625216 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 35330297 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625280 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625344 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 34699425 d89 d90
private def d84 : MobiusHarmonicTree := .branch 70029722 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625408 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625472 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 32498751 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625536 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625600 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 30299003 d96 d97
private def d91 : MobiusHarmonicTree := .branch 62797754 d92 d95
private def d83 : MobiusHarmonicTree := .branch 132827476 d84 d91
private def d67 : MobiusHarmonicTree := .branch 276902396 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625664 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625728 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 30708362 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625792 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625856 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 30542276 d105 d106
private def d100 : MobiusHarmonicTree := .branch 61250638 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625920 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 625984 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 29173415 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626048 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626112 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 26351586 d112 d113
private def d107 : MobiusHarmonicTree := .branch 55525001 d108 d111
private def d99 : MobiusHarmonicTree := .branch 116775639 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626176 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626240 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 26991354 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626304 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626368 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 26345599 d120 d121
private def d115 : MobiusHarmonicTree := .branch 53336953 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626432 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626496 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 23845439 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626560 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626624 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 22544707 d127 d128
private def d122 : MobiusHarmonicTree := .branch 46390146 d123 d126
private def d114 : MobiusHarmonicTree := .branch 99727099 d115 d122
private def d98 : MobiusHarmonicTree := .branch 216502738 d99 d114
private def d66 : MobiusHarmonicTree := .branch 493405134 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1013958770 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626688 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626752 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 21257298 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626816 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626880 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 21996290 d138 d139
private def d133 : MobiusHarmonicTree := .branch 43253588 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 626944 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627008 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 22130609 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627072 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627136 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 21363890 d145 d146
private def d140 : MobiusHarmonicTree := .branch 43494499 d141 d144
private def d132 : MobiusHarmonicTree := .branch 86748087 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627200 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627264 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 19424125 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627328 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627392 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 20049785 d153 d154
private def d148 : MobiusHarmonicTree := .branch 39473910 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627456 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627520 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 17196354 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627584 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627648 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 16781828 d160 d161
private def d155 : MobiusHarmonicTree := .branch 33978182 d156 d159
private def d147 : MobiusHarmonicTree := .branch 73452092 d148 d155
private def d131 : MobiusHarmonicTree := .branch 160200179 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627712 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627776 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 13899945 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627840 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627904 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 12059270 d169 d170
private def d164 : MobiusHarmonicTree := .branch 25959215 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 627968 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628032 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 10052147 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628096 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628160 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 8938878 d176 d177
private def d171 : MobiusHarmonicTree := .branch 18991025 d172 d175
private def d163 : MobiusHarmonicTree := .branch 44950240 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628224 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628288 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 8080770 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628352 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628416 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 7272313 d184 d185
private def d179 : MobiusHarmonicTree := .branch 15353083 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628480 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628544 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6987668 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628608 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628672 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 5828236 d191 d192
private def d186 : MobiusHarmonicTree := .branch 12815904 d187 d190
private def d178 : MobiusHarmonicTree := .branch 28168987 d179 d186
private def d162 : MobiusHarmonicTree := .branch 73119227 d163 d178
private def d130 : MobiusHarmonicTree := .branch 233319406 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628736 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628800 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 5849249 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628864 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628928 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 6358535 d201 d202
private def d196 : MobiusHarmonicTree := .branch 12207784 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 628992 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629056 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 7352341 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629120 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629184 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 6567316 d208 d209
private def d203 : MobiusHarmonicTree := .branch 13919657 d204 d207
private def d195 : MobiusHarmonicTree := .branch 26127441 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629248 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629312 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 7522562 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629376 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629440 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 7749848 d216 d217
private def d211 : MobiusHarmonicTree := .branch 15272410 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629504 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629568 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 8898195 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629632 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629696 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 10111274 d223 d224
private def d218 : MobiusHarmonicTree := .branch 19009469 d219 d222
private def d210 : MobiusHarmonicTree := .branch 34281879 d211 d218
private def d194 : MobiusHarmonicTree := .branch 60409320 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629760 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629824 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 10872931 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629888 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 629952 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 10926313 d232 d233
private def d227 : MobiusHarmonicTree := .branch 21799244 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630016 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630080 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 7481729 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630144 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630208 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 7183357 d239 d240
private def d234 : MobiusHarmonicTree := .branch 14665086 d235 d238
private def d226 : MobiusHarmonicTree := .branch 36464330 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630272 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630336 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 9488687 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630400 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630464 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 6672921 d247 d248
private def d242 : MobiusHarmonicTree := .branch 16161608 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630528 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630592 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 5358555 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630656 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock076 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630720 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 2378355 d254 d255
private def d249 : MobiusHarmonicTree := .branch 7736910 d250 d253
private def d241 : MobiusHarmonicTree := .branch 23898518 d242 d249
private def d225 : MobiusHarmonicTree := .branch 60362848 d226 d241
private def d193 : MobiusHarmonicTree := .branch 120772168 d194 d225
private def d129 : MobiusHarmonicTree := .branch 354091574 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1368050344 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630784 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630848 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 318693 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630912 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 630976 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 453300 d266 d267
private def d261 : MobiusHarmonicTree := .branch 771993 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631040 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631104 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 2142343 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631168 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631232 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 1066249 d273 d274
private def d268 : MobiusHarmonicTree := .branch 3208592 d269 d272
private def d260 : MobiusHarmonicTree := .branch 3980585 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631296 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631360 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 451447 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631424 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631488 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 1461647 d281 d282
private def d276 : MobiusHarmonicTree := .branch 1913094 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631552 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631616 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 4577198 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631680 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631744 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 4288213 d288 d289
private def d283 : MobiusHarmonicTree := .branch 8865411 d284 d287
private def d275 : MobiusHarmonicTree := .branch 10778505 d276 d283
private def d259 : MobiusHarmonicTree := .branch 14759090 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631808 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631872 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 5274818 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 631936 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632000 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 7911430 d297 d298
private def d292 : MobiusHarmonicTree := .branch 13186248 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632064 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632128 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 9376307 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632192 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632256 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 10918097 d304 d305
private def d299 : MobiusHarmonicTree := .branch 20294404 d300 d303
private def d291 : MobiusHarmonicTree := .branch 33480652 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632320 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632384 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 12701202 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632448 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632512 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 11588796 d312 d313
private def d307 : MobiusHarmonicTree := .branch 24289998 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632576 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632640 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 9937824 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632704 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632768 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 7138612 d319 d320
private def d314 : MobiusHarmonicTree := .branch 17076436 d315 d318
private def d306 : MobiusHarmonicTree := .branch 41366434 d307 d314
private def d290 : MobiusHarmonicTree := .branch 74847086 d291 d306
private def d258 : MobiusHarmonicTree := .branch 89606176 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632832 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632896 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 5809857 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 632960 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633024 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 7510068 d329 d330
private def d324 : MobiusHarmonicTree := .branch 13319925 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633088 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633152 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 9343790 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633216 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633280 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 8506576 d336 d337
private def d331 : MobiusHarmonicTree := .branch 17850366 d332 d335
private def d323 : MobiusHarmonicTree := .branch 31170291 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633344 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633408 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 7609728 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633472 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633536 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 5306876 d344 d345
private def d339 : MobiusHarmonicTree := .branch 12916604 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633600 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633664 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 2209461 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633728 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633792 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 899394 d351 d352
private def d346 : MobiusHarmonicTree := .branch 3108855 d347 d350
private def d338 : MobiusHarmonicTree := .branch 16025459 d339 d346
private def d322 : MobiusHarmonicTree := .branch 47195750 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633856 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633920 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 1033295 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 633984 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634048 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 1894234 d360 d361
private def d355 : MobiusHarmonicTree := .branch 2927529 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634112 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634176 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 2690157 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634240 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634304 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 4480592 d367 d368
private def d362 : MobiusHarmonicTree := .branch 7170749 d363 d366
private def d354 : MobiusHarmonicTree := .branch 10098278 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634368 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634432 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 3951605 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634496 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634560 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 4552786 d375 d376
private def d370 : MobiusHarmonicTree := .branch 8504391 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634624 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634688 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 7523417 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634752 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634816 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 7950410 d382 d383
private def d377 : MobiusHarmonicTree := .branch 15473827 d378 d381
private def d369 : MobiusHarmonicTree := .branch 23978218 d370 d377
private def d353 : MobiusHarmonicTree := .branch 34076496 d354 d369
private def d321 : MobiusHarmonicTree := .branch 81272246 d322 d353
private def d257 : MobiusHarmonicTree := .branch 170878422 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634880 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 634944 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 7334543 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635008 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635072 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 8455805 d393 d394
private def d388 : MobiusHarmonicTree := .branch 15790348 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635136 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635200 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 6746025 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635264 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635328 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 6635976 d400 d401
private def d395 : MobiusHarmonicTree := .branch 13382001 d396 d399
private def d387 : MobiusHarmonicTree := .branch 29172349 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635392 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635456 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 8126493 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635520 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635584 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 6998412 d408 d409
private def d403 : MobiusHarmonicTree := .branch 15124905 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635648 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635712 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 5769975 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635776 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635840 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 7299034 d415 d416
private def d410 : MobiusHarmonicTree := .branch 13069009 d411 d414
private def d402 : MobiusHarmonicTree := .branch 28193914 d403 d410
private def d386 : MobiusHarmonicTree := .branch 57366263 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635904 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 635968 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 7563355 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636032 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636096 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 8182782 d424 d425
private def d419 : MobiusHarmonicTree := .branch 15746137 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636160 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636224 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 9114780 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636288 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636352 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 9810705 d431 d432
private def d426 : MobiusHarmonicTree := .branch 18925485 d427 d430
private def d418 : MobiusHarmonicTree := .branch 34671622 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636416 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636480 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 7799243 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636544 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636608 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 6751500 d439 d440
private def d434 : MobiusHarmonicTree := .branch 14550743 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636672 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636736 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 7037487 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636800 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636864 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 7461654 d446 d447
private def d441 : MobiusHarmonicTree := .branch 14499141 d442 d445
private def d433 : MobiusHarmonicTree := .branch 29049884 d434 d441
private def d417 : MobiusHarmonicTree := .branch 63721506 d418 d433
private def d385 : MobiusHarmonicTree := .branch 121087769 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636928 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 636992 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 7425564 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637056 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637120 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 7951470 d456 d457
private def d451 : MobiusHarmonicTree := .branch 15377034 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637184 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637248 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 7880822 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637312 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637376 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 8798681 d463 d464
private def d458 : MobiusHarmonicTree := .branch 16679503 d459 d462
private def d450 : MobiusHarmonicTree := .branch 32056537 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637440 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637504 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 7883931 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637568 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637632 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 8958189 d471 d472
private def d466 : MobiusHarmonicTree := .branch 16842120 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637696 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637760 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 10417754 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637824 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637888 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 11502100 d478 d479
private def d473 : MobiusHarmonicTree := .branch 21919854 d474 d477
private def d465 : MobiusHarmonicTree := .branch 38761974 d466 d473
private def d449 : MobiusHarmonicTree := .branch 70818511 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 637952 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638016 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 8576704 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638080 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638144 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 7689560 d487 d488
private def d482 : MobiusHarmonicTree := .branch 16266264 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638208 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638272 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 8541884 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638336 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638400 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 8037352 d494 d495
private def d489 : MobiusHarmonicTree := .branch 16579236 d490 d493
private def d481 : MobiusHarmonicTree := .branch 32845500 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638464 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638528 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 7794606 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638592 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638656 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 5356646 d502 d503
private def d497 : MobiusHarmonicTree := .branch 13151252 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638720 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638784 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 3553760 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638848 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock077 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 638912 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 989297 d509 d510
private def d504 : MobiusHarmonicTree := .branch 4543057 d505 d508
private def d496 : MobiusHarmonicTree := .branch 17694309 d497 d504
private def d480 : MobiusHarmonicTree := .branch 50539809 d481 d496
private def d448 : MobiusHarmonicTree := .branch 121358320 d449 d480
private def d384 : MobiusHarmonicTree := .branch 242446089 d385 d448
private def d256 : MobiusHarmonicTree := .branch 413324511 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1781374855 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 622592 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 622592 1781374855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 622592 1368050344 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 622592 1013958770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 622592 520553636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 622592 256019711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 622592 132980150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 622592 67085129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622592 34426830 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622720 32658299 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 622848 65895021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622848 32319266 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622976 33575755 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 623104 123039561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 623104 63456410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 623104 31290245 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 623232 32166165 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 623360 59583151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 623360 31514787 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 623488 28068364 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 623616 264533925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 623616 120316986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 623616 58166402 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 623616 28158703 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 623744 30007699 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 623872 62150584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 623872 30185870 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624000 31964714 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 624128 144216939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 624128 70900246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624128 34140185 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624256 36760061 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 624384 73316693 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624384 36818229 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624512 36498464 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 624640 493405134 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 624640 276902396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 624640 144074920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 624640 70965751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624640 35745005 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624768 35220746 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 624896 73109169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 624896 35787944 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625024 37321225 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 625152 132827476 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 625152 70029722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625152 35330297 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625280 34699425 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 625408 62797754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625408 32498751 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625536 30299003 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 625664 216502738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 625664 116775639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 625664 61250638 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625664 30708362 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625792 30542276 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 625920 55525001 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 625920 29173415 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626048 26351586 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 626176 99727099 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 626176 53336953 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626176 26991354 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626304 26345599 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 626432 46390146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626432 23845439 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626560 22544707 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 626688 354091574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 626688 233319406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 626688 160200179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 626688 86748087 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 626688 43253588 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626688 21257298 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626816 21996290 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 626944 43494499 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 626944 22130609 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627072 21363890 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 627200 73452092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 627200 39473910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627200 19424125 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627328 20049785 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 627456 33978182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627456 17196354 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627584 16781828 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 627712 73119227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 627712 44950240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 627712 25959215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627712 13899945 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627840 12059270 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 627968 18991025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 627968 10052147 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628096 8938878 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 628224 28168987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 628224 15353083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628224 8080770 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628352 7272313 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 628480 12815904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628480 6987668 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628608 5828236 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 628736 120772168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 628736 60409320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 628736 26127441 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 628736 12207784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628736 5849249 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628864 6358535 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 628992 13919657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 628992 7352341 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 629120 6567316 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 629248 34281879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 629248 15272410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 629248 7522562 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 629376 7749848 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 629504 19009469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 629504 8898195 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 629632 10111274 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 629760 60362848 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 629760 36464330 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 629760 21799244 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 629760 10872931 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 629888 10926313 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 630016 14665086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630016 7481729 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630144 7183357 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 630272 23898518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 630272 16161608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630272 9488687 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630400 6672921 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 630528 7736910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630528 5358555 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630656 2378355 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 630784 413324511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 630784 170878422 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 630784 89606176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 630784 14759090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 630784 3980585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 630784 771993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630784 318693 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 630912 453300 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 631040 3208592 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631040 2142343 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631168 1066249 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 631296 10778505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 631296 1913094 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631296 451447 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631424 1461647 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 631552 8865411 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631552 4577198 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631680 4288213 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 631808 74847086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 631808 33480652 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 631808 13186248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631808 5274818 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 631936 7911430 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 632064 20294404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632064 9376307 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632192 10918097 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 632320 41366434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 632320 24289998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632320 12701202 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632448 11588796 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 632576 17076436 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632576 9937824 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632704 7138612 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 632832 81272246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 632832 47195750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 632832 31170291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 632832 13319925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632832 5809857 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 632960 7510068 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 633088 17850366 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633088 9343790 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633216 8506576 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 633344 16025459 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 633344 12916604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633344 7609728 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633472 5306876 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 633600 3108855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633600 2209461 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633728 899394 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 633856 34076496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 633856 10098278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 633856 2927529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633856 1033295 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 633984 1894234 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 634112 7170749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 634112 2690157 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 634240 4480592 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 634368 23978218 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 634368 8504391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 634368 3951605 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 634496 4552786 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 634624 15473827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 634624 7523417 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 634752 7950410 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 634880 242446089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 634880 121087769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 634880 57366263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 634880 29172349 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 634880 15790348 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 634880 7334543 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635008 8455805 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 635136 13382001 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635136 6746025 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635264 6635976 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 635392 28193914 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 635392 15124905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635392 8126493 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635520 6998412 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 635648 13069009 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635648 5769975 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635776 7299034 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 635904 63721506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 635904 34671622 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 635904 15746137 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 635904 7563355 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636032 8182782 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 636160 18925485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636160 9114780 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636288 9810705 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 636416 29049884 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 636416 14550743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636416 7799243 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636544 6751500 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 636672 14499141 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636672 7037487 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636800 7461654 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 636928 121358320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 636928 70818511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 636928 32056537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 636928 15377034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 636928 7425564 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637056 7951470 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 637184 16679503 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637184 7880822 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637312 8798681 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 637440 38761974 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 637440 16842120 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637440 7883931 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637568 8958189 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 637696 21919854 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637696 10417754 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637824 11502100 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 637952 50539809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 637952 32845500 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 637952 16266264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 637952 8576704 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638080 7689560 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 638208 16579236 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638208 8541884 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638336 8037352 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 638464 17694309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 638464 13151252 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638464 7794606 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638592 5356646 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 638720 4543057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638720 3553760 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 638848 989297 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 622592 (MobiusHarmonicTree.branch 1781374855 mobiusHarmonicBlock076 mobiusHarmonicBlock077) = true := Helfgott.combined

#print axioms solution
