-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair029_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:42:16.899706+00:00
-- url     : https://prove2.me/submissions/32edd592-210b-4156-9330-c7d1fcce9693

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475136 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475200 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 17649558 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475264 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475328 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 15947021 d11 d12
private def d6 : MobiusHarmonicTree := .branch 33596579 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475392 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475456 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 13080182 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475520 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475584 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 12592991 d18 d19
private def d13 : MobiusHarmonicTree := .branch 25673173 d14 d17
private def d5 : MobiusHarmonicTree := .branch 59269752 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475648 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475712 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 11250608 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475776 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475840 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 10654988 d26 d27
private def d21 : MobiusHarmonicTree := .branch 21905596 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475904 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475968 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 10112058 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476032 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476096 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 7782201 d33 d34
private def d28 : MobiusHarmonicTree := .branch 17894259 d29 d32
private def d20 : MobiusHarmonicTree := .branch 39799855 d21 d28
private def d4 : MobiusHarmonicTree := .branch 99069607 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476160 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476224 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 8498162 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476288 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476352 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 12847660 d42 d43
private def d37 : MobiusHarmonicTree := .branch 21345822 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476416 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476480 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 12300749 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476544 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476608 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 10350342 d49 d50
private def d44 : MobiusHarmonicTree := .branch 22651091 d45 d48
private def d36 : MobiusHarmonicTree := .branch 43996913 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476672 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476736 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 11020800 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476800 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476864 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 10198011 d57 d58
private def d52 : MobiusHarmonicTree := .branch 21218811 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476928 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 476992 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 9342013 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477056 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477120 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 10881949 d64 d65
private def d59 : MobiusHarmonicTree := .branch 20223962 d60 d63
private def d51 : MobiusHarmonicTree := .branch 41442773 d52 d59
private def d35 : MobiusHarmonicTree := .branch 85439686 d36 d51
private def d3 : MobiusHarmonicTree := .branch 184509293 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477184 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477248 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 13418689 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477312 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477376 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 13712496 d74 d75
private def d69 : MobiusHarmonicTree := .branch 27131185 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477440 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477504 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 15819889 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477568 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477632 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 15317261 d81 d82
private def d76 : MobiusHarmonicTree := .branch 31137150 d77 d80
private def d68 : MobiusHarmonicTree := .branch 58268335 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477696 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477760 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 15690103 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477824 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477888 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 12191284 d89 d90
private def d84 : MobiusHarmonicTree := .branch 27881387 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 477952 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478016 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 9127482 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478080 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478144 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 7552207 d96 d97
private def d91 : MobiusHarmonicTree := .branch 16679689 d92 d95
private def d83 : MobiusHarmonicTree := .branch 44561076 d84 d91
private def d67 : MobiusHarmonicTree := .branch 102829411 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478208 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478272 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 5986161 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478336 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478400 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 6214683 d105 d106
private def d100 : MobiusHarmonicTree := .branch 12200844 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478464 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478528 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 3636166 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478592 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478656 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 4623419 d112 d113
private def d107 : MobiusHarmonicTree := .branch 8259585 d108 d111
private def d99 : MobiusHarmonicTree := .branch 20460429 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478720 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478784 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 4684888 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478848 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478912 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 4117707 d120 d121
private def d115 : MobiusHarmonicTree := .branch 8802595 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 478976 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479040 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 4663524 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479104 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479168 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 7289785 d127 d128
private def d122 : MobiusHarmonicTree := .branch 11953309 d123 d126
private def d114 : MobiusHarmonicTree := .branch 20755904 d115 d122
private def d98 : MobiusHarmonicTree := .branch 41216333 d99 d114
private def d66 : MobiusHarmonicTree := .branch 144045744 d67 d98
private def d2 : MobiusHarmonicTree := .branch 328555037 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479232 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479296 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 5583299 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479360 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479424 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 7823962 d138 d139
private def d133 : MobiusHarmonicTree := .branch 13407261 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479488 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479552 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 8370383 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479616 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479680 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 9437499 d145 d146
private def d140 : MobiusHarmonicTree := .branch 17807882 d141 d144
private def d132 : MobiusHarmonicTree := .branch 31215143 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479744 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479808 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 12148673 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479872 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 479936 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 11580780 d153 d154
private def d148 : MobiusHarmonicTree := .branch 23729453 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480000 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480064 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 12106797 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480128 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480192 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 10400105 d160 d161
private def d155 : MobiusHarmonicTree := .branch 22506902 d156 d159
private def d147 : MobiusHarmonicTree := .branch 46236355 d148 d155
private def d131 : MobiusHarmonicTree := .branch 77451498 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480256 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480320 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 12589638 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480384 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480448 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 9695213 d169 d170
private def d164 : MobiusHarmonicTree := .branch 22284851 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480512 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480576 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 5938903 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480640 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480704 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 5666679 d176 d177
private def d171 : MobiusHarmonicTree := .branch 11605582 d172 d175
private def d163 : MobiusHarmonicTree := .branch 33890433 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480768 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480832 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 6503421 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480896 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 480960 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 5096126 d184 d185
private def d179 : MobiusHarmonicTree := .branch 11599547 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481024 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481088 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 2136947 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481152 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481216 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 399049 d191 d192
private def d186 : MobiusHarmonicTree := .branch 2535996 d187 d190
private def d178 : MobiusHarmonicTree := .branch 14135543 d179 d186
private def d162 : MobiusHarmonicTree := .branch 48025976 d163 d178
private def d130 : MobiusHarmonicTree := .branch 125477474 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481280 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481344 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 639907 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481408 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481472 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 1429049 d201 d202
private def d196 : MobiusHarmonicTree := .branch 2068956 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481536 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481600 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 1490937 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481664 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481728 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 1403263 d208 d209
private def d203 : MobiusHarmonicTree := .branch 2894200 d204 d207
private def d195 : MobiusHarmonicTree := .branch 4963156 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481792 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481856 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 2992738 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481920 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 481984 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 3207660 d216 d217
private def d211 : MobiusHarmonicTree := .branch 6200398 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482048 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482112 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 3092657 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482176 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482240 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 3203842 d223 d224
private def d218 : MobiusHarmonicTree := .branch 6296499 d219 d222
private def d210 : MobiusHarmonicTree := .branch 12496897 d211 d218
private def d194 : MobiusHarmonicTree := .branch 17460053 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482304 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482368 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 5261615 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482432 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482496 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 3796993 d232 d233
private def d227 : MobiusHarmonicTree := .branch 9058608 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482560 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482624 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 3667529 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482688 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482752 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 694032 d239 d240
private def d234 : MobiusHarmonicTree := .branch 4361561 d235 d238
private def d226 : MobiusHarmonicTree := .branch 13420169 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482816 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482880 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 892628 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 482944 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483008 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 879909 d247 d248
private def d242 : MobiusHarmonicTree := .branch 1772537 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483072 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483136 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 749342 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483200 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock058 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483264 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 846404 d254 d255
private def d249 : MobiusHarmonicTree := .branch 1595746 d250 d253
private def d241 : MobiusHarmonicTree := .branch 3368283 d242 d249
private def d225 : MobiusHarmonicTree := .branch 16788452 d226 d241
private def d193 : MobiusHarmonicTree := .branch 34248505 d194 d225
private def d129 : MobiusHarmonicTree := .branch 159725979 d130 d193
private def d1 : MobiusHarmonicTree := .branch 488281016 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483328 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483392 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 1264070 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483456 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483520 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 941092 d266 d267
private def d261 : MobiusHarmonicTree := .branch 2205162 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483584 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483648 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 1108259 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483712 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483776 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 2226230 d273 d274
private def d268 : MobiusHarmonicTree := .branch 3334489 d269 d272
private def d260 : MobiusHarmonicTree := .branch 5539651 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483840 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483904 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 5769788 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 483968 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484032 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 6276521 d281 d282
private def d276 : MobiusHarmonicTree := .branch 12046309 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484096 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484160 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 5306192 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484224 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484288 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 5232480 d288 d289
private def d283 : MobiusHarmonicTree := .branch 10538672 d284 d287
private def d275 : MobiusHarmonicTree := .branch 22584981 d276 d283
private def d259 : MobiusHarmonicTree := .branch 28124632 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484352 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484416 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 6773164 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484480 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484544 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 6028392 d297 d298
private def d292 : MobiusHarmonicTree := .branch 12801556 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484608 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484672 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 3988270 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484736 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484800 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 6303691 d304 d305
private def d299 : MobiusHarmonicTree := .branch 10291961 d300 d303
private def d291 : MobiusHarmonicTree := .branch 23093517 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484864 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484928 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 9553940 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 484992 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485056 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 11536897 d312 d313
private def d307 : MobiusHarmonicTree := .branch 21090837 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485120 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485184 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 12294326 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485248 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485312 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 16309064 d319 d320
private def d314 : MobiusHarmonicTree := .branch 28603390 d315 d318
private def d306 : MobiusHarmonicTree := .branch 49694227 d307 d314
private def d290 : MobiusHarmonicTree := .branch 72787744 d291 d306
private def d258 : MobiusHarmonicTree := .branch 100912376 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485376 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485440 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 16183418 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485504 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485568 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 16945199 d329 d330
private def d324 : MobiusHarmonicTree := .branch 33128617 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485632 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485696 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 17955776 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485760 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485824 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 19752059 d336 d337
private def d331 : MobiusHarmonicTree := .branch 37707835 d332 d335
private def d323 : MobiusHarmonicTree := .branch 70836452 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485888 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 485952 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 19685163 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486016 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486080 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 18402491 d344 d345
private def d339 : MobiusHarmonicTree := .branch 38087654 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486144 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486208 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 15211729 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486272 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486336 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 15495550 d351 d352
private def d346 : MobiusHarmonicTree := .branch 30707279 d347 d350
private def d338 : MobiusHarmonicTree := .branch 68794933 d339 d346
private def d322 : MobiusHarmonicTree := .branch 139631385 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486400 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486464 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 13803828 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486528 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486592 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 11048469 d360 d361
private def d355 : MobiusHarmonicTree := .branch 24852297 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486656 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486720 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 4423652 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486784 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486848 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 4524989 d367 d368
private def d362 : MobiusHarmonicTree := .branch 8948641 d363 d366
private def d354 : MobiusHarmonicTree := .branch 33800938 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486912 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 486976 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 5390581 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487040 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487104 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 3880144 d375 d376
private def d370 : MobiusHarmonicTree := .branch 9270725 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487168 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487232 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 4975112 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487296 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487360 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 3603219 d382 d383
private def d377 : MobiusHarmonicTree := .branch 8578331 d378 d381
private def d369 : MobiusHarmonicTree := .branch 17849056 d370 d377
private def d353 : MobiusHarmonicTree := .branch 51649994 d354 d369
private def d321 : MobiusHarmonicTree := .branch 191281379 d322 d353
private def d257 : MobiusHarmonicTree := .branch 292193755 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487424 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487488 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 1103694 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487552 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487616 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 2959337 d393 d394
private def d388 : MobiusHarmonicTree := .branch 4063031 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487680 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487744 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 2089320 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487808 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487872 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 858887 d400 d401
private def d395 : MobiusHarmonicTree := .branch 2948207 d396 d399
private def d387 : MobiusHarmonicTree := .branch 7011238 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 487936 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488000 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 3631086 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488064 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488128 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 6344788 d408 d409
private def d403 : MobiusHarmonicTree := .branch 9975874 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488192 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488256 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 3727625 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488320 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488384 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 3095993 d415 d416
private def d410 : MobiusHarmonicTree := .branch 6823618 d411 d414
private def d402 : MobiusHarmonicTree := .branch 16799492 d403 d410
private def d386 : MobiusHarmonicTree := .branch 23810730 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488448 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488512 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 2990790 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488576 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488640 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 2670753 d424 d425
private def d419 : MobiusHarmonicTree := .branch 5661543 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488704 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488768 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 3019916 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488832 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488896 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 1595483 d431 d432
private def d426 : MobiusHarmonicTree := .branch 4615399 d427 d430
private def d418 : MobiusHarmonicTree := .branch 10276942 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 488960 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489024 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 4705275 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489088 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489152 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 4368920 d439 d440
private def d434 : MobiusHarmonicTree := .branch 9074195 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489216 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489280 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 2358653 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489344 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489408 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 1293497 d446 d447
private def d441 : MobiusHarmonicTree := .branch 3652150 d442 d445
private def d433 : MobiusHarmonicTree := .branch 12726345 d434 d441
private def d417 : MobiusHarmonicTree := .branch 23003287 d418 d433
private def d385 : MobiusHarmonicTree := .branch 46814017 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489472 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489536 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 3243851 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489600 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489664 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 5469120 d456 d457
private def d451 : MobiusHarmonicTree := .branch 8712971 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489728 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489792 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 5633155 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489856 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489920 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 2908730 d463 d464
private def d458 : MobiusHarmonicTree := .branch 8541885 d459 d462
private def d450 : MobiusHarmonicTree := .branch 17254856 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 489984 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490048 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 3601711 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490112 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490176 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 2670559 d471 d472
private def d466 : MobiusHarmonicTree := .branch 6272270 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490240 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490304 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 1558274 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490368 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490432 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 984923 d478 d479
private def d473 : MobiusHarmonicTree := .branch 2543197 d474 d477
private def d465 : MobiusHarmonicTree := .branch 8815467 d466 d473
private def d449 : MobiusHarmonicTree := .branch 26070323 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490496 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490560 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 744090 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490624 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490688 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 521771 d487 d488
private def d482 : MobiusHarmonicTree := .branch 1265861 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490752 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490816 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 1424241 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490880 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 490944 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 2265083 d494 d495
private def d489 : MobiusHarmonicTree := .branch 3689324 d490 d493
private def d481 : MobiusHarmonicTree := .branch 4955185 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491008 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491072 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 2639117 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491136 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491200 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 2512319 d502 d503
private def d497 : MobiusHarmonicTree := .branch 5151436 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491264 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491328 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 3350190 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491392 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock059 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 491456 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 3904720 d509 d510
private def d504 : MobiusHarmonicTree := .branch 7254910 d505 d508
private def d496 : MobiusHarmonicTree := .branch 12406346 d497 d504
private def d480 : MobiusHarmonicTree := .branch 17361531 d481 d496
private def d448 : MobiusHarmonicTree := .branch 43431854 d449 d480
private def d384 : MobiusHarmonicTree := .branch 90245871 d385 d448
private def d256 : MobiusHarmonicTree := .branch 382439626 d257 d384
private def d0 : MobiusHarmonicTree := .branch 870720642 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 475136 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 475136 870720642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 475136 488281016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 475136 328555037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 475136 184509293 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 475136 99069607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 475136 59269752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 475136 33596579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475136 17649558 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475264 15947021 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 475392 25673173 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475392 13080182 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475520 12592991 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 475648 39799855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 475648 21905596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475648 11250608 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475776 10654988 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 475904 17894259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475904 10112058 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476032 7782201 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 476160 85439686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 476160 43996913 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 476160 21345822 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476160 8498162 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476288 12847660 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 476416 22651091 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476416 12300749 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476544 10350342 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 476672 41442773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 476672 21218811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476672 11020800 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476800 10198011 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 476928 20223962 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 476928 9342013 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477056 10881949 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 477184 144045744 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 477184 102829411 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 477184 58268335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 477184 27131185 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477184 13418689 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477312 13712496 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 477440 31137150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477440 15819889 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477568 15317261 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 477696 44561076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 477696 27881387 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477696 15690103 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477824 12191284 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 477952 16679689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 477952 9127482 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478080 7552207 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 478208 41216333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 478208 20460429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 478208 12200844 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478208 5986161 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478336 6214683 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 478464 8259585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478464 3636166 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478592 4623419 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 478720 20755904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 478720 8802595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478720 4684888 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478848 4117707 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 478976 11953309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 478976 4663524 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 479104 7289785 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 479232 159725979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 479232 125477474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 479232 77451498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 479232 31215143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 479232 13407261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 479232 5583299 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 479360 7823962 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 479488 17807882 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 479488 8370383 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 479616 9437499 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 479744 46236355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 479744 23729453 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 479744 12148673 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 479872 11580780 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 480000 22506902 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480000 12106797 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480128 10400105 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 480256 48025976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 480256 33890433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 480256 22284851 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480256 12589638 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480384 9695213 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 480512 11605582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480512 5938903 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480640 5666679 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 480768 14135543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 480768 11599547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480768 6503421 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 480896 5096126 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 481024 2535996 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481024 2136947 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481152 399049 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 481280 34248505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 481280 17460053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 481280 4963156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 481280 2068956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481280 639907 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481408 1429049 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 481536 2894200 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481536 1490937 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481664 1403263 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 481792 12496897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 481792 6200398 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481792 2992738 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 481920 3207660 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 482048 6296499 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482048 3092657 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482176 3203842 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 482304 16788452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 482304 13420169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 482304 9058608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482304 5261615 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482432 3796993 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 482560 4361561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482560 3667529 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482688 694032 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 482816 3368283 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 482816 1772537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482816 892628 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 482944 879909 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 483072 1595746 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483072 749342 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483200 846404 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 483328 382439626 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 483328 292193755 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 483328 100912376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 483328 28124632 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 483328 5539651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 483328 2205162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483328 1264070 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483456 941092 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 483584 3334489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483584 1108259 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483712 2226230 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 483840 22584981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 483840 12046309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483840 5769788 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 483968 6276521 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 484096 10538672 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484096 5306192 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484224 5232480 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 484352 72787744 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 484352 23093517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 484352 12801556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484352 6773164 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484480 6028392 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 484608 10291961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484608 3988270 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484736 6303691 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 484864 49694227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 484864 21090837 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484864 9553940 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 484992 11536897 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 485120 28603390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 485120 12294326 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 485248 16309064 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 485376 191281379 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 485376 139631385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 485376 70836452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 485376 33128617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 485376 16183418 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 485504 16945199 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 485632 37707835 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 485632 17955776 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 485760 19752059 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 485888 68794933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 485888 38087654 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 485888 19685163 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486016 18402491 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 486144 30707279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486144 15211729 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486272 15495550 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 486400 51649994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 486400 33800938 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 486400 24852297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486400 13803828 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486528 11048469 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 486656 8948641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486656 4423652 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486784 4524989 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 486912 17849056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 486912 9270725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 486912 5390581 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487040 3880144 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 487168 8578331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487168 4975112 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487296 3603219 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 487424 90245871 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 487424 46814017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 487424 23810730 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 487424 7011238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 487424 4063031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487424 1103694 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487552 2959337 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 487680 2948207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487680 2089320 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487808 858887 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 487936 16799492 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 487936 9975874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 487936 3631086 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488064 6344788 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 488192 6823618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488192 3727625 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488320 3095993 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 488448 23003287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 488448 10276942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 488448 5661543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488448 2990790 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488576 2670753 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 488704 4615399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488704 3019916 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488832 1595483 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 488960 12726345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 488960 9074195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 488960 4705275 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489088 4368920 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 489216 3652150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489216 2358653 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489344 1293497 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 489472 43431854 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 489472 26070323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 489472 17254856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 489472 8712971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489472 3243851 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489600 5469120 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 489728 8541885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489728 5633155 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489856 2908730 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 489984 8815467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 489984 6272270 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 489984 3601711 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 490112 2670559 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 490240 2543197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 490240 1558274 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 490368 984923 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 490496 17361531 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 490496 4955185 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 490496 1265861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 490496 744090 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 490624 521771 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 490752 3689324 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 490752 1424241 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 490880 2265083 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 491008 12406346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 491008 5151436 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491008 2639117 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491136 2512319 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 491264 7254910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491264 3350190 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 491392 3904720 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 475136 (MobiusHarmonicTree.branch 870720642 mobiusHarmonicBlock058 mobiusHarmonicBlock059) = true := Helfgott.combined

#print axioms solution
