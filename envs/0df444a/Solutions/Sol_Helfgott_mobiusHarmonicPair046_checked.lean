-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair046_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:43:55.014912+00:00
-- url     : https://prove2.me/submissions/29857b1c-021e-4be8-b43e-a22b6f686e1d

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753664 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753728 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 17643073 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753792 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753856 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 17397289 d11 d12
private def d6 : MobiusHarmonicTree := .branch 35040362 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753920 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 753984 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 16797533 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754048 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754112 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 14479385 d18 d19
private def d13 : MobiusHarmonicTree := .branch 31276918 d14 d17
private def d5 : MobiusHarmonicTree := .branch 66317280 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754176 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754240 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 15011211 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754304 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754368 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 14063506 d26 d27
private def d21 : MobiusHarmonicTree := .branch 29074717 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754432 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754496 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 14016046 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754560 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754624 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 14564930 d33 d34
private def d28 : MobiusHarmonicTree := .branch 28580976 d29 d32
private def d20 : MobiusHarmonicTree := .branch 57655693 d21 d28
private def d4 : MobiusHarmonicTree := .branch 123972973 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754688 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754752 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 14369046 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754816 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754880 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 14300369 d42 d43
private def d37 : MobiusHarmonicTree := .branch 28669415 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 754944 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755008 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 13765484 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755072 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755136 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 15411878 d49 d50
private def d44 : MobiusHarmonicTree := .branch 29177362 d45 d48
private def d36 : MobiusHarmonicTree := .branch 57846777 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755200 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755264 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 14775019 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755328 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755392 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 14182132 d57 d58
private def d52 : MobiusHarmonicTree := .branch 28957151 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755456 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755520 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 13053355 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755584 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755648 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 12745442 d64 d65
private def d59 : MobiusHarmonicTree := .branch 25798797 d60 d63
private def d51 : MobiusHarmonicTree := .branch 54755948 d52 d59
private def d35 : MobiusHarmonicTree := .branch 112602725 d36 d51
private def d3 : MobiusHarmonicTree := .branch 236575698 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755712 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755776 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 11488947 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755840 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755904 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 10758070 d74 d75
private def d69 : MobiusHarmonicTree := .branch 22247017 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 755968 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756032 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 11020734 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756096 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756160 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 10960748 d81 d82
private def d76 : MobiusHarmonicTree := .branch 21981482 d77 d80
private def d68 : MobiusHarmonicTree := .branch 44228499 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756224 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756288 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 9914295 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756352 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756416 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 10005128 d89 d90
private def d84 : MobiusHarmonicTree := .branch 19919423 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756480 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756544 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 11395297 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756608 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756672 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 11114548 d96 d97
private def d91 : MobiusHarmonicTree := .branch 22509845 d92 d95
private def d83 : MobiusHarmonicTree := .branch 42429268 d84 d91
private def d67 : MobiusHarmonicTree := .branch 86657767 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756736 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756800 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 10923733 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756864 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756928 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 10640435 d105 d106
private def d100 : MobiusHarmonicTree := .branch 21564168 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 756992 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757056 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 13469310 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757120 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757184 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 15617154 d112 d113
private def d107 : MobiusHarmonicTree := .branch 29086464 d108 d111
private def d99 : MobiusHarmonicTree := .branch 50650632 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757248 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757312 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 15469248 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757376 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757440 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 15997399 d120 d121
private def d115 : MobiusHarmonicTree := .branch 31466647 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757504 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757568 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 15124812 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757632 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757696 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 15351879 d127 d128
private def d122 : MobiusHarmonicTree := .branch 30476691 d123 d126
private def d114 : MobiusHarmonicTree := .branch 61943338 d115 d122
private def d98 : MobiusHarmonicTree := .branch 112593970 d99 d114
private def d66 : MobiusHarmonicTree := .branch 199251737 d67 d98
private def d2 : MobiusHarmonicTree := .branch 435827435 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757760 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757824 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 16068418 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757888 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 757952 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 16862622 d138 d139
private def d133 : MobiusHarmonicTree := .branch 32931040 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758016 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758080 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 17736987 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758144 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758208 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 18526644 d145 d146
private def d140 : MobiusHarmonicTree := .branch 36263631 d141 d144
private def d132 : MobiusHarmonicTree := .branch 69194671 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758272 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758336 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 17895862 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758400 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758464 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 17275768 d153 d154
private def d148 : MobiusHarmonicTree := .branch 35171630 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758528 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758592 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 18804611 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758656 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758720 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 20677042 d160 d161
private def d155 : MobiusHarmonicTree := .branch 39481653 d156 d159
private def d147 : MobiusHarmonicTree := .branch 74653283 d148 d155
private def d131 : MobiusHarmonicTree := .branch 143847954 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758784 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758848 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 19641714 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758912 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 758976 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 18401223 d169 d170
private def d164 : MobiusHarmonicTree := .branch 38042937 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759040 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759104 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 18150420 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759168 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759232 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 18583321 d176 d177
private def d171 : MobiusHarmonicTree := .branch 36733741 d172 d175
private def d163 : MobiusHarmonicTree := .branch 74776678 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759296 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759360 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 18000767 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759424 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759488 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 18068811 d184 d185
private def d179 : MobiusHarmonicTree := .branch 36069578 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759552 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759616 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 17308863 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759680 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759744 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 16468767 d191 d192
private def d186 : MobiusHarmonicTree := .branch 33777630 d187 d190
private def d178 : MobiusHarmonicTree := .branch 69847208 d179 d186
private def d162 : MobiusHarmonicTree := .branch 144623886 d163 d178
private def d130 : MobiusHarmonicTree := .branch 288471840 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759808 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759872 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 17021371 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 759936 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760000 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 16468493 d201 d202
private def d196 : MobiusHarmonicTree := .branch 33489864 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760064 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760128 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 16801191 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760192 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760256 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 16313004 d208 d209
private def d203 : MobiusHarmonicTree := .branch 33114195 d204 d207
private def d195 : MobiusHarmonicTree := .branch 66604059 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760320 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760384 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 15834171 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760448 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760512 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 15476505 d216 d217
private def d211 : MobiusHarmonicTree := .branch 31310676 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760576 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760640 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 15648701 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760704 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760768 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 15709216 d223 d224
private def d218 : MobiusHarmonicTree := .branch 31357917 d219 d222
private def d210 : MobiusHarmonicTree := .branch 62668593 d211 d218
private def d194 : MobiusHarmonicTree := .branch 129272652 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760832 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760896 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 14720887 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 760960 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761024 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 15054796 d232 d233
private def d227 : MobiusHarmonicTree := .branch 29775683 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761088 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761152 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 13999916 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761216 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761280 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 13825487 d239 d240
private def d234 : MobiusHarmonicTree := .branch 27825403 d235 d238
private def d226 : MobiusHarmonicTree := .branch 57601086 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761344 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761408 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 12270775 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761472 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761536 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 11023855 d247 d248
private def d242 : MobiusHarmonicTree := .branch 23294630 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761600 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761664 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 10658327 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761728 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock092 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761792 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 11746070 d254 d255
private def d249 : MobiusHarmonicTree := .branch 22404397 d250 d253
private def d241 : MobiusHarmonicTree := .branch 45699027 d242 d249
private def d225 : MobiusHarmonicTree := .branch 103300113 d226 d241
private def d193 : MobiusHarmonicTree := .branch 232572765 d194 d225
private def d129 : MobiusHarmonicTree := .branch 521044605 d130 d193
private def d1 : MobiusHarmonicTree := .branch 956872040 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761856 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761920 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 10985457 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 761984 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762048 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 13005794 d266 d267
private def d261 : MobiusHarmonicTree := .branch 23991251 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762112 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762176 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 14820783 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762240 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762304 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 14342116 d273 d274
private def d268 : MobiusHarmonicTree := .branch 29162899 d269 d272
private def d260 : MobiusHarmonicTree := .branch 53154150 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762368 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762432 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 14314788 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762496 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762560 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 13939981 d281 d282
private def d276 : MobiusHarmonicTree := .branch 28254769 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762624 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762688 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 15198884 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762752 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762816 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 16738097 d288 d289
private def d283 : MobiusHarmonicTree := .branch 31936981 d284 d287
private def d275 : MobiusHarmonicTree := .branch 60191750 d276 d283
private def d259 : MobiusHarmonicTree := .branch 113345900 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762880 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 762944 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 15331481 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763008 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763072 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 13068292 d297 d298
private def d292 : MobiusHarmonicTree := .branch 28399773 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763136 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763200 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 14976453 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763264 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763328 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 16500183 d304 d305
private def d299 : MobiusHarmonicTree := .branch 31476636 d300 d303
private def d291 : MobiusHarmonicTree := .branch 59876409 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763392 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763456 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 14873279 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763520 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763584 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 13401347 d312 d313
private def d307 : MobiusHarmonicTree := .branch 28274626 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763648 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763712 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 13933336 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763776 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763840 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 13292134 d319 d320
private def d314 : MobiusHarmonicTree := .branch 27225470 d315 d318
private def d306 : MobiusHarmonicTree := .branch 55500096 d307 d314
private def d290 : MobiusHarmonicTree := .branch 115376505 d291 d306
private def d258 : MobiusHarmonicTree := .branch 228722405 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763904 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 763968 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 12497972 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764032 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764096 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 12045700 d329 d330
private def d324 : MobiusHarmonicTree := .branch 24543672 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764160 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764224 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 11241524 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764288 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764352 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 9813636 d336 d337
private def d331 : MobiusHarmonicTree := .branch 21055160 d332 d335
private def d323 : MobiusHarmonicTree := .branch 45598832 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764416 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764480 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 9259937 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764544 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764608 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 9121096 d344 d345
private def d339 : MobiusHarmonicTree := .branch 18381033 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764672 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764736 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 8349359 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764800 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764864 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 8213313 d351 d352
private def d346 : MobiusHarmonicTree := .branch 16562672 d347 d350
private def d338 : MobiusHarmonicTree := .branch 34943705 d339 d346
private def d322 : MobiusHarmonicTree := .branch 80542537 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764928 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 764992 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 7664215 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765056 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765120 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 6536299 d360 d361
private def d355 : MobiusHarmonicTree := .branch 14200514 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765184 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765248 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 6938981 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765312 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765376 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 7498350 d367 d368
private def d362 : MobiusHarmonicTree := .branch 14437331 d363 d366
private def d354 : MobiusHarmonicTree := .branch 28637845 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765440 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765504 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 7899434 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765568 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765632 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 9197692 d375 d376
private def d370 : MobiusHarmonicTree := .branch 17097126 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765696 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765760 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 10508583 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765824 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765888 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 8484380 d382 d383
private def d377 : MobiusHarmonicTree := .branch 18992963 d378 d381
private def d369 : MobiusHarmonicTree := .branch 36090089 d370 d377
private def d353 : MobiusHarmonicTree := .branch 64727934 d354 d369
private def d321 : MobiusHarmonicTree := .branch 145270471 d322 d353
private def d257 : MobiusHarmonicTree := .branch 373992876 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 765952 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766016 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 7250560 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766080 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766144 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 7259786 d393 d394
private def d388 : MobiusHarmonicTree := .branch 14510346 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766208 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766272 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 7836720 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766336 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766400 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 7528769 d400 d401
private def d395 : MobiusHarmonicTree := .branch 15365489 d396 d399
private def d387 : MobiusHarmonicTree := .branch 29875835 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766464 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766528 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 6875238 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766592 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766656 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 8059720 d408 d409
private def d403 : MobiusHarmonicTree := .branch 14934958 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766720 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766784 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 9745967 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766848 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766912 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 9325798 d415 d416
private def d410 : MobiusHarmonicTree := .branch 19071765 d411 d414
private def d402 : MobiusHarmonicTree := .branch 34006723 d403 d410
private def d386 : MobiusHarmonicTree := .branch 63882558 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 766976 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767040 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 9067412 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767104 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767168 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 9675889 d424 d425
private def d419 : MobiusHarmonicTree := .branch 18743301 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767232 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767296 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 12164863 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767360 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767424 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 12467759 d431 d432
private def d426 : MobiusHarmonicTree := .branch 24632622 d427 d430
private def d418 : MobiusHarmonicTree := .branch 43375923 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767488 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767552 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 12861742 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767616 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767680 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 14672839 d439 d440
private def d434 : MobiusHarmonicTree := .branch 27534581 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767744 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767808 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 13511281 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767872 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 767936 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 13249832 d446 d447
private def d441 : MobiusHarmonicTree := .branch 26761113 d442 d445
private def d433 : MobiusHarmonicTree := .branch 54295694 d434 d441
private def d417 : MobiusHarmonicTree := .branch 97671617 d418 d433
private def d385 : MobiusHarmonicTree := .branch 161554175 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768000 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768064 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 15007909 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768128 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768192 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 15269734 d456 d457
private def d451 : MobiusHarmonicTree := .branch 30277643 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768256 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768320 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 13754787 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768384 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768448 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 12447251 d463 d464
private def d458 : MobiusHarmonicTree := .branch 26202038 d459 d462
private def d450 : MobiusHarmonicTree := .branch 56479681 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768512 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768576 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 13309093 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768640 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768704 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 12750108 d471 d472
private def d466 : MobiusHarmonicTree := .branch 26059201 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768768 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768832 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 11629431 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768896 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768960 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 11038341 d478 d479
private def d473 : MobiusHarmonicTree := .branch 22667772 d474 d477
private def d465 : MobiusHarmonicTree := .branch 48726973 d466 d473
private def d449 : MobiusHarmonicTree := .branch 105206654 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769024 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769088 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 11567029 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769152 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769216 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 11554683 d487 d488
private def d482 : MobiusHarmonicTree := .branch 23121712 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769280 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769344 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 10973055 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769408 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769472 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 11513161 d494 d495
private def d489 : MobiusHarmonicTree := .branch 22486216 d490 d493
private def d481 : MobiusHarmonicTree := .branch 45607928 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769536 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769600 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 10347027 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769664 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769728 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 10634981 d502 d503
private def d497 : MobiusHarmonicTree := .branch 20982008 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769792 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769856 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 11517782 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769920 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock093 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 769984 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 11688621 d509 d510
private def d504 : MobiusHarmonicTree := .branch 23206403 d505 d508
private def d496 : MobiusHarmonicTree := .branch 44188411 d497 d504
private def d480 : MobiusHarmonicTree := .branch 89796339 d481 d496
private def d448 : MobiusHarmonicTree := .branch 195002993 d449 d480
private def d384 : MobiusHarmonicTree := .branch 356557168 d385 d448
private def d256 : MobiusHarmonicTree := .branch 730550044 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1687422084 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 753664 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 753664 1687422084 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 753664 956872040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 753664 435827435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 753664 236575698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 753664 123972973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 753664 66317280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 753664 35040362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753664 17643073 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753792 17397289 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 753920 31276918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 753920 16797533 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754048 14479385 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 754176 57655693 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 754176 29074717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754176 15011211 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754304 14063506 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 754432 28580976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754432 14016046 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754560 14564930 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 754688 112602725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 754688 57846777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 754688 28669415 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754688 14369046 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754816 14300369 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 754944 29177362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 754944 13765484 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755072 15411878 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 755200 54755948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 755200 28957151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755200 14775019 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755328 14182132 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 755456 25798797 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755456 13053355 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755584 12745442 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 755712 199251737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 755712 86657767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 755712 44228499 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 755712 22247017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755712 11488947 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755840 10758070 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 755968 21981482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 755968 11020734 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756096 10960748 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 756224 42429268 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 756224 19919423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756224 9914295 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756352 10005128 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 756480 22509845 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756480 11395297 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756608 11114548 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 756736 112593970 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 756736 50650632 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 756736 21564168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756736 10923733 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756864 10640435 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 756992 29086464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 756992 13469310 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 757120 15617154 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 757248 61943338 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 757248 31466647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 757248 15469248 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 757376 15997399 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 757504 30476691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 757504 15124812 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 757632 15351879 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 757760 521044605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 757760 288471840 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 757760 143847954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 757760 69194671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 757760 32931040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 757760 16068418 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 757888 16862622 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 758016 36263631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758016 17736987 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758144 18526644 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 758272 74653283 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 758272 35171630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758272 17895862 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758400 17275768 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 758528 39481653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758528 18804611 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758656 20677042 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 758784 144623886 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 758784 74776678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 758784 38042937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758784 19641714 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 758912 18401223 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 759040 36733741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759040 18150420 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759168 18583321 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 759296 69847208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 759296 36069578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759296 18000767 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759424 18068811 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 759552 33777630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759552 17308863 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759680 16468767 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 759808 232572765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 759808 129272652 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 759808 66604059 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 759808 33489864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759808 17021371 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 759936 16468493 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 760064 33114195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760064 16801191 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760192 16313004 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 760320 62668593 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 760320 31310676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760320 15834171 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760448 15476505 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 760576 31357917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760576 15648701 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760704 15709216 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 760832 103300113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 760832 57601086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 760832 29775683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760832 14720887 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 760960 15054796 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 761088 27825403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761088 13999916 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761216 13825487 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 761344 45699027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 761344 23294630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761344 12270775 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761472 11023855 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 761600 22404397 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761600 10658327 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761728 11746070 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 761856 730550044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 761856 373992876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 761856 228722405 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 761856 113345900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 761856 53154150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 761856 23991251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761856 10985457 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 761984 13005794 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 762112 29162899 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 762112 14820783 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 762240 14342116 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 762368 60191750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 762368 28254769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 762368 14314788 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 762496 13939981 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 762624 31936981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 762624 15198884 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 762752 16738097 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 762880 115376505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 762880 59876409 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 762880 28399773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 762880 15331481 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763008 13068292 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 763136 31476636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763136 14976453 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763264 16500183 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 763392 55500096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 763392 28274626 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763392 14873279 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763520 13401347 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 763648 27225470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763648 13933336 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763776 13292134 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 763904 145270471 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 763904 80542537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 763904 45598832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 763904 24543672 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 763904 12497972 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764032 12045700 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 764160 21055160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764160 11241524 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764288 9813636 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 764416 34943705 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 764416 18381033 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764416 9259937 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764544 9121096 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 764672 16562672 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764672 8349359 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764800 8213313 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 764928 64727934 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 764928 28637845 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 764928 14200514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 764928 7664215 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765056 6536299 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 765184 14437331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765184 6938981 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765312 7498350 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 765440 36090089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 765440 17097126 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765440 7899434 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765568 9197692 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 765696 18992963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765696 10508583 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765824 8484380 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 765952 356557168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 765952 161554175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 765952 63882558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 765952 29875835 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 765952 14510346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 765952 7250560 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766080 7259786 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 766208 15365489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766208 7836720 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766336 7528769 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 766464 34006723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 766464 14934958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766464 6875238 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766592 8059720 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 766720 19071765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766720 9745967 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766848 9325798 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 766976 97671617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 766976 43375923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 766976 18743301 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 766976 9067412 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 767104 9675889 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 767232 24632622 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 767232 12164863 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 767360 12467759 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 767488 54295694 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 767488 27534581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 767488 12861742 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 767616 14672839 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 767744 26761113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 767744 13511281 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 767872 13249832 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 768000 195002993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 768000 105206654 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 768000 56479681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 768000 30277643 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768000 15007909 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768128 15269734 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 768256 26202038 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768256 13754787 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768384 12447251 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 768512 48726973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 768512 26059201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768512 13309093 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768640 12750108 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 768768 22667772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768768 11629431 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768896 11038341 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 769024 89796339 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 769024 45607928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 769024 23121712 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769024 11567029 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769152 11554683 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 769280 22486216 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769280 10973055 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769408 11513161 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 769536 44188411 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 769536 20982008 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769536 10347027 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769664 10634981 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 769792 23206403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769792 11517782 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 769920 11688621 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 753664 (MobiusHarmonicTree.branch 1687422084 mobiusHarmonicBlock092 mobiusHarmonicBlock093) = true := Helfgott.combined

#print axioms solution
