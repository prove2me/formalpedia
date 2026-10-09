-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair053_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:11:03.216991+00:00
-- url     : https://prove2.me/submissions/9e8022f5-3589-4818-b41f-ff0ed77a13f3

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868352 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868416 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 19535635 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868480 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868544 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 20593150 d11 d12
private def d6 : MobiusHarmonicTree := .branch 40128785 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868608 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868672 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 20971147 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868736 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868800 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 22101836 d18 d19
private def d13 : MobiusHarmonicTree := .branch 43072983 d14 d17
private def d5 : MobiusHarmonicTree := .branch 83201768 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868864 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868928 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 21321763 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868992 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869056 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 21343901 d26 d27
private def d21 : MobiusHarmonicTree := .branch 42665664 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869120 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869184 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 21559405 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869248 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869312 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 20073422 d33 d34
private def d28 : MobiusHarmonicTree := .branch 41632827 d29 d32
private def d20 : MobiusHarmonicTree := .branch 84298491 d21 d28
private def d4 : MobiusHarmonicTree := .branch 167500259 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869376 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869440 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 20271722 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869504 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869568 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 20622977 d42 d43
private def d37 : MobiusHarmonicTree := .branch 40894699 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869632 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869696 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 19169999 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869760 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869824 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 20616880 d49 d50
private def d44 : MobiusHarmonicTree := .branch 39786879 d45 d48
private def d36 : MobiusHarmonicTree := .branch 80681578 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869888 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 869952 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 20639136 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870016 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870080 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 19587969 d57 d58
private def d52 : MobiusHarmonicTree := .branch 40227105 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870144 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870208 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 19249490 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870272 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870336 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 18591780 d64 d65
private def d59 : MobiusHarmonicTree := .branch 37841270 d60 d63
private def d51 : MobiusHarmonicTree := .branch 78068375 d52 d59
private def d35 : MobiusHarmonicTree := .branch 158749953 d36 d51
private def d3 : MobiusHarmonicTree := .branch 326250212 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870400 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870464 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 17362094 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870528 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870592 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 15549286 d74 d75
private def d69 : MobiusHarmonicTree := .branch 32911380 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870656 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870720 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 14857903 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870784 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870848 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 15278277 d81 d82
private def d76 : MobiusHarmonicTree := .branch 30136180 d77 d80
private def d68 : MobiusHarmonicTree := .branch 63047560 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870912 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 870976 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 16183056 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871040 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871104 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 15511463 d89 d90
private def d84 : MobiusHarmonicTree := .branch 31694519 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871168 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871232 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 14294778 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871296 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871360 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 13345892 d96 d97
private def d91 : MobiusHarmonicTree := .branch 27640670 d92 d95
private def d83 : MobiusHarmonicTree := .branch 59335189 d84 d91
private def d67 : MobiusHarmonicTree := .branch 122382749 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871424 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871488 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 11918791 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871552 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871616 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 10797256 d105 d106
private def d100 : MobiusHarmonicTree := .branch 22716047 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871680 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871744 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 10490535 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871808 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871872 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 10279113 d112 d113
private def d107 : MobiusHarmonicTree := .branch 20769648 d108 d111
private def d99 : MobiusHarmonicTree := .branch 43485695 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 871936 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872000 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 10403743 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872064 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872128 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 10430867 d120 d121
private def d115 : MobiusHarmonicTree := .branch 20834610 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872192 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872256 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 12535336 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872320 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872384 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 14313695 d127 d128
private def d122 : MobiusHarmonicTree := .branch 26849031 d123 d126
private def d114 : MobiusHarmonicTree := .branch 47683641 d115 d122
private def d98 : MobiusHarmonicTree := .branch 91169336 d99 d114
private def d66 : MobiusHarmonicTree := .branch 213552085 d67 d98
private def d2 : MobiusHarmonicTree := .branch 539802297 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872448 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872512 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 15415329 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872576 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872640 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 14871048 d138 d139
private def d133 : MobiusHarmonicTree := .branch 30286377 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872704 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872768 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 15005183 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872832 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872896 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 14783081 d145 d146
private def d140 : MobiusHarmonicTree := .branch 29788264 d141 d144
private def d132 : MobiusHarmonicTree := .branch 60074641 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 872960 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873024 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 13244846 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873088 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873152 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 13747986 d153 d154
private def d148 : MobiusHarmonicTree := .branch 26992832 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873216 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873280 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 12607704 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873344 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873408 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 13544701 d160 d161
private def d155 : MobiusHarmonicTree := .branch 26152405 d156 d159
private def d147 : MobiusHarmonicTree := .branch 53145237 d148 d155
private def d131 : MobiusHarmonicTree := .branch 113219878 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873472 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873536 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 13100858 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873600 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873664 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 12452221 d169 d170
private def d164 : MobiusHarmonicTree := .branch 25553079 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873728 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873792 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 12369157 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873856 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873920 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 11876461 d176 d177
private def d171 : MobiusHarmonicTree := .branch 24245618 d172 d175
private def d163 : MobiusHarmonicTree := .branch 49798697 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 873984 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874048 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 11355277 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874112 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874176 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 11847799 d184 d185
private def d179 : MobiusHarmonicTree := .branch 23203076 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874240 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874304 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 11412583 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874368 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874432 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 11999866 d191 d192
private def d186 : MobiusHarmonicTree := .branch 23412449 d187 d190
private def d178 : MobiusHarmonicTree := .branch 46615525 d179 d186
private def d162 : MobiusHarmonicTree := .branch 96414222 d163 d178
private def d130 : MobiusHarmonicTree := .branch 209634100 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874496 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874560 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 11358929 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874624 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874688 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 11582475 d201 d202
private def d196 : MobiusHarmonicTree := .branch 22941404 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874752 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874816 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 13429160 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874880 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 874944 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 14523296 d208 d209
private def d203 : MobiusHarmonicTree := .branch 27952456 d204 d207
private def d195 : MobiusHarmonicTree := .branch 50893860 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875008 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875072 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 12578490 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875136 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875200 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 11840784 d216 d217
private def d211 : MobiusHarmonicTree := .branch 24419274 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875264 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875328 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 13529850 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875392 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875456 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 14699833 d223 d224
private def d218 : MobiusHarmonicTree := .branch 28229683 d219 d222
private def d210 : MobiusHarmonicTree := .branch 52648957 d211 d218
private def d194 : MobiusHarmonicTree := .branch 103542817 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875520 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875584 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 15276708 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875648 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875712 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 16651674 d232 d233
private def d227 : MobiusHarmonicTree := .branch 31928382 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875776 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875840 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 17760137 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875904 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 875968 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 18270162 d239 d240
private def d234 : MobiusHarmonicTree := .branch 36030299 d235 d238
private def d226 : MobiusHarmonicTree := .branch 67958681 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876032 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876096 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 19344972 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876160 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876224 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 20737909 d247 d248
private def d242 : MobiusHarmonicTree := .branch 40082881 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876288 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876352 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 22080230 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876416 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock106 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876480 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 23440415 d254 d255
private def d249 : MobiusHarmonicTree := .branch 45520645 d250 d253
private def d241 : MobiusHarmonicTree := .branch 85603526 d242 d249
private def d225 : MobiusHarmonicTree := .branch 153562207 d226 d241
private def d193 : MobiusHarmonicTree := .branch 257105024 d194 d225
private def d129 : MobiusHarmonicTree := .branch 466739124 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1006541421 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876544 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876608 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 23667413 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876672 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876736 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 23427897 d266 d267
private def d261 : MobiusHarmonicTree := .branch 47095310 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876800 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876864 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 23385675 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876928 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 876992 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 23641111 d273 d274
private def d268 : MobiusHarmonicTree := .branch 47026786 d269 d272
private def d260 : MobiusHarmonicTree := .branch 94122096 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877056 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877120 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 21973135 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877184 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877248 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 22090742 d281 d282
private def d276 : MobiusHarmonicTree := .branch 44063877 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877312 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877376 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 22828367 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877440 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877504 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 22830731 d288 d289
private def d283 : MobiusHarmonicTree := .branch 45659098 d284 d287
private def d275 : MobiusHarmonicTree := .branch 89722975 d276 d283
private def d259 : MobiusHarmonicTree := .branch 183845071 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877568 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877632 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 23546381 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877696 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877760 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 23421075 d297 d298
private def d292 : MobiusHarmonicTree := .branch 46967456 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877824 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877888 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 23411929 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 877952 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878016 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 23802610 d304 d305
private def d299 : MobiusHarmonicTree := .branch 47214539 d300 d303
private def d291 : MobiusHarmonicTree := .branch 94181995 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878080 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878144 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 24720377 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878208 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878272 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 25090265 d312 d313
private def d307 : MobiusHarmonicTree := .branch 49810642 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878336 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878400 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 24387606 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878464 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878528 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 22863346 d319 d320
private def d314 : MobiusHarmonicTree := .branch 47250952 d315 d318
private def d306 : MobiusHarmonicTree := .branch 97061594 d307 d314
private def d290 : MobiusHarmonicTree := .branch 191243589 d291 d306
private def d258 : MobiusHarmonicTree := .branch 375088660 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878592 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878656 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 22325063 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878720 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878784 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 22795216 d329 d330
private def d324 : MobiusHarmonicTree := .branch 45120279 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878848 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878912 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 22659932 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 878976 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879040 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 23490468 d336 d337
private def d331 : MobiusHarmonicTree := .branch 46150400 d332 d335
private def d323 : MobiusHarmonicTree := .branch 91270679 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879104 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879168 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 24406098 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879232 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879296 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 24350252 d344 d345
private def d339 : MobiusHarmonicTree := .branch 48756350 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879360 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879424 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 22437510 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879488 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879552 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 20758393 d351 d352
private def d346 : MobiusHarmonicTree := .branch 43195903 d347 d350
private def d338 : MobiusHarmonicTree := .branch 91952253 d339 d346
private def d322 : MobiusHarmonicTree := .branch 183222932 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879616 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879680 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 21152078 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879744 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879808 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 19876035 d360 d361
private def d355 : MobiusHarmonicTree := .branch 41028113 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879872 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 879936 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 20532227 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880000 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880064 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 22254123 d367 d368
private def d362 : MobiusHarmonicTree := .branch 42786350 d363 d366
private def d354 : MobiusHarmonicTree := .branch 83814463 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880128 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880192 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 23160931 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880256 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880320 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 24291222 d375 d376
private def d370 : MobiusHarmonicTree := .branch 47452153 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880384 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880448 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 24129855 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880512 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880576 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 23606213 d382 d383
private def d377 : MobiusHarmonicTree := .branch 47736068 d378 d381
private def d369 : MobiusHarmonicTree := .branch 95188221 d370 d377
private def d353 : MobiusHarmonicTree := .branch 179002684 d354 d369
private def d321 : MobiusHarmonicTree := .branch 362225616 d322 d353
private def d257 : MobiusHarmonicTree := .branch 737314276 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880640 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880704 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 24126203 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880768 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880832 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 24209011 d393 d394
private def d388 : MobiusHarmonicTree := .branch 48335214 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880896 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 880960 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 25181684 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881024 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881088 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 26183597 d400 d401
private def d395 : MobiusHarmonicTree := .branch 51365281 d396 d399
private def d387 : MobiusHarmonicTree := .branch 99700495 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881152 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881216 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 26245645 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881280 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881344 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 25405591 d408 d409
private def d403 : MobiusHarmonicTree := .branch 51651236 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881408 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881472 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 25698002 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881536 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881600 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 24960411 d415 d416
private def d410 : MobiusHarmonicTree := .branch 50658413 d411 d414
private def d402 : MobiusHarmonicTree := .branch 102309649 d403 d410
private def d386 : MobiusHarmonicTree := .branch 202010144 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881664 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881728 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 23007194 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881792 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881856 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 22419844 d424 d425
private def d419 : MobiusHarmonicTree := .branch 45427038 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881920 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 881984 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 22615011 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882048 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882112 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 21374960 d431 d432
private def d426 : MobiusHarmonicTree := .branch 43989971 d427 d430
private def d418 : MobiusHarmonicTree := .branch 89417009 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882176 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882240 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 20802787 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882304 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882368 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 20493794 d439 d440
private def d434 : MobiusHarmonicTree := .branch 41296581 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882432 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882496 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 19976399 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882560 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882624 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 19213235 d446 d447
private def d441 : MobiusHarmonicTree := .branch 39189634 d442 d445
private def d433 : MobiusHarmonicTree := .branch 80486215 d434 d441
private def d417 : MobiusHarmonicTree := .branch 169903224 d418 d433
private def d385 : MobiusHarmonicTree := .branch 371913368 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882688 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882752 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 17186141 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882816 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882880 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 16118906 d456 d457
private def d451 : MobiusHarmonicTree := .branch 33305047 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 882944 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883008 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 15560560 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883072 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883136 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 13752203 d463 d464
private def d458 : MobiusHarmonicTree := .branch 29312763 d459 d462
private def d450 : MobiusHarmonicTree := .branch 62617810 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883200 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883264 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 14598192 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883328 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883392 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 16798929 d471 d472
private def d466 : MobiusHarmonicTree := .branch 31397121 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883456 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883520 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 17664645 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883584 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883648 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 17795620 d478 d479
private def d473 : MobiusHarmonicTree := .branch 35460265 d474 d477
private def d465 : MobiusHarmonicTree := .branch 66857386 d466 d473
private def d449 : MobiusHarmonicTree := .branch 129475196 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883712 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883776 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 19473300 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883840 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883904 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 20444616 d487 d488
private def d482 : MobiusHarmonicTree := .branch 39917916 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 883968 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884032 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 20529879 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884096 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884160 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 21552721 d494 d495
private def d489 : MobiusHarmonicTree := .branch 42082600 d490 d493
private def d481 : MobiusHarmonicTree := .branch 82000516 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884224 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884288 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 21298607 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884352 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884416 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 19391420 d502 d503
private def d497 : MobiusHarmonicTree := .branch 40690027 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884480 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884544 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 18553152 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884608 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock107 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 884672 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 17283317 d509 d510
private def d504 : MobiusHarmonicTree := .branch 35836469 d505 d508
private def d496 : MobiusHarmonicTree := .branch 76526496 d497 d504
private def d480 : MobiusHarmonicTree := .branch 158527012 d481 d496
private def d448 : MobiusHarmonicTree := .branch 288002208 d449 d480
private def d384 : MobiusHarmonicTree := .branch 659915576 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1397229852 d257 d384
private def d0 : MobiusHarmonicTree := .branch 2403771273 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 868352 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 868352 2403771273 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 868352 1006541421 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 868352 539802297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 868352 326250212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 868352 167500259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 868352 83201768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 868352 40128785 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868352 19535635 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868480 20593150 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 868608 43072983 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868608 20971147 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868736 22101836 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 868864 84298491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 868864 42665664 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868864 21321763 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868992 21343901 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 869120 41632827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 869120 21559405 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 869248 20073422 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 869376 158749953 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 869376 80681578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 869376 40894699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 869376 20271722 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 869504 20622977 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 869632 39786879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 869632 19169999 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 869760 20616880 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 869888 78068375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 869888 40227105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 869888 20639136 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870016 19587969 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 870144 37841270 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870144 19249490 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870272 18591780 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 870400 213552085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 870400 122382749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 870400 63047560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 870400 32911380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870400 17362094 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870528 15549286 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 870656 30136180 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870656 14857903 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870784 15278277 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 870912 59335189 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 870912 31694519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 870912 16183056 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871040 15511463 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 871168 27640670 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871168 14294778 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871296 13345892 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 871424 91169336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 871424 43485695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 871424 22716047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871424 11918791 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871552 10797256 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 871680 20769648 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871680 10490535 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871808 10279113 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 871936 47683641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 871936 20834610 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 871936 10403743 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872064 10430867 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 872192 26849031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872192 12535336 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872320 14313695 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 872448 466739124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 872448 209634100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 872448 113219878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 872448 60074641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 872448 30286377 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872448 15415329 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872576 14871048 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 872704 29788264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872704 15005183 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872832 14783081 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 872960 53145237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 872960 26992832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 872960 13244846 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873088 13747986 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 873216 26152405 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873216 12607704 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873344 13544701 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 873472 96414222 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 873472 49798697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 873472 25553079 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873472 13100858 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873600 12452221 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 873728 24245618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873728 12369157 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873856 11876461 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 873984 46615525 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 873984 23203076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 873984 11355277 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 874112 11847799 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 874240 23412449 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 874240 11412583 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 874368 11999866 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 874496 257105024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 874496 103542817 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 874496 50893860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 874496 22941404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 874496 11358929 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 874624 11582475 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 874752 27952456 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 874752 13429160 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 874880 14523296 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 875008 52648957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 875008 24419274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875008 12578490 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875136 11840784 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 875264 28229683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875264 13529850 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875392 14699833 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 875520 153562207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 875520 67958681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 875520 31928382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875520 15276708 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875648 16651674 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 875776 36030299 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875776 17760137 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 875904 18270162 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 876032 85603526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 876032 40082881 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876032 19344972 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876160 20737909 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 876288 45520645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876288 22080230 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876416 23440415 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 876544 1397229852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 876544 737314276 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 876544 375088660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 876544 183845071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 876544 94122096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 876544 47095310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876544 23667413 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876672 23427897 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 876800 47026786 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876800 23385675 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 876928 23641111 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 877056 89722975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 877056 44063877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877056 21973135 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877184 22090742 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 877312 45659098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877312 22828367 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877440 22830731 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 877568 191243589 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 877568 94181995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 877568 46967456 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877568 23546381 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877696 23421075 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 877824 47214539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877824 23411929 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 877952 23802610 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 878080 97061594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 878080 49810642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878080 24720377 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878208 25090265 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 878336 47250952 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878336 24387606 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878464 22863346 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 878592 362225616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 878592 183222932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 878592 91270679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 878592 45120279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878592 22325063 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878720 22795216 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 878848 46150400 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878848 22659932 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 878976 23490468 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 879104 91952253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 879104 48756350 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 879104 24406098 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 879232 24350252 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 879360 43195903 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 879360 22437510 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 879488 20758393 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 879616 179002684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 879616 83814463 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 879616 41028113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 879616 21152078 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 879744 19876035 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 879872 42786350 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 879872 20532227 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880000 22254123 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 880128 95188221 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 880128 47452153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880128 23160931 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880256 24291222 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 880384 47736068 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880384 24129855 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880512 23606213 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 880640 659915576 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 880640 371913368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 880640 202010144 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 880640 99700495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 880640 48335214 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880640 24126203 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880768 24209011 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 880896 51365281 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 880896 25181684 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881024 26183597 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 881152 102309649 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 881152 51651236 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881152 26245645 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881280 25405591 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 881408 50658413 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881408 25698002 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881536 24960411 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 881664 169903224 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 881664 89417009 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 881664 45427038 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881664 23007194 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881792 22419844 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 881920 43989971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 881920 22615011 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882048 21374960 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 882176 80486215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 882176 41296581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882176 20802787 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882304 20493794 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 882432 39189634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882432 19976399 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882560 19213235 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 882688 288002208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 882688 129475196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 882688 62617810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 882688 33305047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882688 17186141 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882816 16118906 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 882944 29312763 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 882944 15560560 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883072 13752203 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 883200 66857386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 883200 31397121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883200 14598192 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883328 16798929 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 883456 35460265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883456 17664645 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883584 17795620 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 883712 158527012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 883712 82000516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 883712 39917916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883712 19473300 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883840 20444616 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 883968 42082600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 883968 20529879 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884096 21552721 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 884224 76526496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 884224 40690027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884224 21298607 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884352 19391420 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 884480 35836469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884480 18553152 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 884608 17283317 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 868352 (MobiusHarmonicTree.branch 2403771273 mobiusHarmonicBlock106 mobiusHarmonicBlock107) = true := Helfgott.combined

#print axioms solution
