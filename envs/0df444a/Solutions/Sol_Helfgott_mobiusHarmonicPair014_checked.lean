-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair014_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:42:56.454978+00:00
-- url     : https://prove2.me/submissions/f1d5eaaa-e54e-46d6-8b44-eed3376fde97

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229376 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229440 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 55801086 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229504 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229568 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 56528098 d11 d12
private def d6 : MobiusHarmonicTree := .branch 112329184 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229632 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229696 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 61054426 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229760 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229824 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 67677975 d18 d19
private def d13 : MobiusHarmonicTree := .branch 128732401 d14 d17
private def d5 : MobiusHarmonicTree := .branch 241061585 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229888 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229952 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 69679683 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230016 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230080 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 75404123 d26 d27
private def d21 : MobiusHarmonicTree := .branch 145083806 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230144 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230208 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 78329202 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230272 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230336 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 79701025 d33 d34
private def d28 : MobiusHarmonicTree := .branch 158030227 d29 d32
private def d20 : MobiusHarmonicTree := .branch 303114033 d21 d28
private def d4 : MobiusHarmonicTree := .branch 544175618 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230400 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230464 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 80551122 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230528 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230592 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 77032453 d42 d43
private def d37 : MobiusHarmonicTree := .branch 157583575 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230656 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230720 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 76963592 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230784 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230848 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 80438305 d49 d50
private def d44 : MobiusHarmonicTree := .branch 157401897 d45 d48
private def d36 : MobiusHarmonicTree := .branch 314985472 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230912 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 230976 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 79939130 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231040 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231104 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 80133372 d57 d58
private def d52 : MobiusHarmonicTree := .branch 160072502 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231168 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231232 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 70570372 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231296 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231360 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 71853455 d64 d65
private def d59 : MobiusHarmonicTree := .branch 142423827 d60 d63
private def d51 : MobiusHarmonicTree := .branch 302496329 d52 d59
private def d35 : MobiusHarmonicTree := .branch 617481801 d36 d51
private def d3 : MobiusHarmonicTree := .branch 1161657419 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231424 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231488 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 72017407 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231552 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231616 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 69857033 d74 d75
private def d69 : MobiusHarmonicTree := .branch 141874440 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231680 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231744 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 67834330 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231808 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231872 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 63284693 d81 d82
private def d76 : MobiusHarmonicTree := .branch 131119023 d77 d80
private def d68 : MobiusHarmonicTree := .branch 272993463 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 231936 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232000 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 67780499 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232064 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232128 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 63964834 d89 d90
private def d84 : MobiusHarmonicTree := .branch 131745333 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232192 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232256 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 62160465 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232320 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232384 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 59341533 d96 d97
private def d91 : MobiusHarmonicTree := .branch 121501998 d92 d95
private def d83 : MobiusHarmonicTree := .branch 253247331 d84 d91
private def d67 : MobiusHarmonicTree := .branch 526240794 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232448 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232512 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 61025147 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232576 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232640 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 56400565 d105 d106
private def d100 : MobiusHarmonicTree := .branch 117425712 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232704 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232768 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 55020793 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232832 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232896 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 54921712 d112 d113
private def d107 : MobiusHarmonicTree := .branch 109942505 d108 d111
private def d99 : MobiusHarmonicTree := .branch 227368217 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 232960 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233024 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 52759018 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233088 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233152 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 47647242 d120 d121
private def d115 : MobiusHarmonicTree := .branch 100406260 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233216 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233280 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 43518865 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233344 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233408 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 40684476 d127 d128
private def d122 : MobiusHarmonicTree := .branch 84203341 d123 d126
private def d114 : MobiusHarmonicTree := .branch 184609601 d115 d122
private def d98 : MobiusHarmonicTree := .branch 411977818 d99 d114
private def d66 : MobiusHarmonicTree := .branch 938218612 d67 d98
private def d2 : MobiusHarmonicTree := .branch 2099876031 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233472 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233536 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 38876359 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233600 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233664 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 41247234 d138 d139
private def d133 : MobiusHarmonicTree := .branch 80123593 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233728 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233792 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 42431070 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233856 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233920 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 38628997 d145 d146
private def d140 : MobiusHarmonicTree := .branch 81060067 d141 d144
private def d132 : MobiusHarmonicTree := .branch 161183660 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 233984 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234048 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 34895035 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234112 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234176 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 30263540 d153 d154
private def d148 : MobiusHarmonicTree := .branch 65158575 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234240 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234304 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 37459688 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234368 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234432 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 35870035 d160 d161
private def d155 : MobiusHarmonicTree := .branch 73329723 d156 d159
private def d147 : MobiusHarmonicTree := .branch 138488298 d148 d155
private def d131 : MobiusHarmonicTree := .branch 299671958 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234496 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234560 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 30943163 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234624 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234688 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 34833571 d169 d170
private def d164 : MobiusHarmonicTree := .branch 65776734 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234752 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234816 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 36215671 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234880 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 234944 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 38430249 d176 d177
private def d171 : MobiusHarmonicTree := .branch 74645920 d172 d175
private def d163 : MobiusHarmonicTree := .branch 140422654 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235008 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235072 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 41630056 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235136 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235200 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 39944946 d184 d185
private def d179 : MobiusHarmonicTree := .branch 81575002 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235264 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235328 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 36604456 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235392 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235456 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 35072591 d191 d192
private def d186 : MobiusHarmonicTree := .branch 71677047 d187 d190
private def d178 : MobiusHarmonicTree := .branch 153252049 d179 d186
private def d162 : MobiusHarmonicTree := .branch 293674703 d163 d178
private def d130 : MobiusHarmonicTree := .branch 593346661 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235520 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235584 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 31734349 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235648 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235712 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 25209223 d201 d202
private def d196 : MobiusHarmonicTree := .branch 56943572 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235776 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235840 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 21171331 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235904 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 235968 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 19617312 d208 d209
private def d203 : MobiusHarmonicTree := .branch 40788643 d204 d207
private def d195 : MobiusHarmonicTree := .branch 97732215 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236032 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236096 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 21609759 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236160 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236224 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 27063197 d216 d217
private def d211 : MobiusHarmonicTree := .branch 48672956 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236288 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236352 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 26477638 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236416 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236480 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 24708585 d223 d224
private def d218 : MobiusHarmonicTree := .branch 51186223 d219 d222
private def d210 : MobiusHarmonicTree := .branch 99859179 d211 d218
private def d194 : MobiusHarmonicTree := .branch 197591394 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236544 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236608 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 18820273 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236672 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236736 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 20250178 d232 d233
private def d227 : MobiusHarmonicTree := .branch 39070451 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236800 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236864 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 20986655 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236928 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 236992 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 21578727 d239 d240
private def d234 : MobiusHarmonicTree := .branch 42565382 d235 d238
private def d226 : MobiusHarmonicTree := .branch 81635833 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237056 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237120 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 23924891 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237184 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237248 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 22225830 d247 d248
private def d242 : MobiusHarmonicTree := .branch 46150721 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237312 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237376 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 23974568 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237440 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock028 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237504 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 19052612 d254 d255
private def d249 : MobiusHarmonicTree := .branch 43027180 d250 d253
private def d241 : MobiusHarmonicTree := .branch 89177901 d242 d249
private def d225 : MobiusHarmonicTree := .branch 170813734 d226 d241
private def d193 : MobiusHarmonicTree := .branch 368405128 d194 d225
private def d129 : MobiusHarmonicTree := .branch 961751789 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3061627820 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237568 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237632 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 11282435 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237696 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237760 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 12315015 d266 d267
private def d261 : MobiusHarmonicTree := .branch 23597450 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237824 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237888 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 10113948 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 237952 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238016 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 13129295 d273 d274
private def d268 : MobiusHarmonicTree := .branch 23243243 d269 d272
private def d260 : MobiusHarmonicTree := .branch 46840693 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238080 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238144 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 13731303 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238208 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238272 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 15473968 d281 d282
private def d276 : MobiusHarmonicTree := .branch 29205271 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238336 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238400 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 19207270 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238464 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238528 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 18467570 d288 d289
private def d283 : MobiusHarmonicTree := .branch 37674840 d284 d287
private def d275 : MobiusHarmonicTree := .branch 66880111 d276 d283
private def d259 : MobiusHarmonicTree := .branch 113720804 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238592 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238656 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 17334569 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238720 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238784 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 19708340 d297 d298
private def d292 : MobiusHarmonicTree := .branch 37042909 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238848 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238912 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 19040691 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 238976 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239040 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 16357143 d304 d305
private def d299 : MobiusHarmonicTree := .branch 35397834 d300 d303
private def d291 : MobiusHarmonicTree := .branch 72440743 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239104 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239168 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 14090419 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239232 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239296 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 14358779 d312 d313
private def d307 : MobiusHarmonicTree := .branch 28449198 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239360 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239424 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 16978280 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239488 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239552 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 15808641 d319 d320
private def d314 : MobiusHarmonicTree := .branch 32786921 d315 d318
private def d306 : MobiusHarmonicTree := .branch 61236119 d307 d314
private def d290 : MobiusHarmonicTree := .branch 133676862 d291 d306
private def d258 : MobiusHarmonicTree := .branch 247397666 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239616 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239680 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 13739558 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239744 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239808 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 10825695 d329 d330
private def d324 : MobiusHarmonicTree := .branch 24565253 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239872 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 239936 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 12061436 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240000 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240064 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 17490980 d336 d337
private def d331 : MobiusHarmonicTree := .branch 29552416 d332 d335
private def d323 : MobiusHarmonicTree := .branch 54117669 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240128 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240192 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 16083071 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240256 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240320 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 15529434 d344 d345
private def d339 : MobiusHarmonicTree := .branch 31612505 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240384 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240448 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 15916483 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240512 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240576 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 9939008 d351 d352
private def d346 : MobiusHarmonicTree := .branch 25855491 d347 d350
private def d338 : MobiusHarmonicTree := .branch 57467996 d339 d346
private def d322 : MobiusHarmonicTree := .branch 111585665 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240640 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240704 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 11462052 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240768 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240832 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 12942677 d360 d361
private def d355 : MobiusHarmonicTree := .branch 24404729 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240896 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 240960 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 22227831 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241024 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241088 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 24215140 d367 d368
private def d362 : MobiusHarmonicTree := .branch 46442971 d363 d366
private def d354 : MobiusHarmonicTree := .branch 70847700 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241152 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241216 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 24646253 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241280 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241344 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 22171706 d375 d376
private def d370 : MobiusHarmonicTree := .branch 46817959 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241408 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241472 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 24122967 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241536 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241600 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 25186220 d382 d383
private def d377 : MobiusHarmonicTree := .branch 49309187 d378 d381
private def d369 : MobiusHarmonicTree := .branch 96127146 d370 d377
private def d353 : MobiusHarmonicTree := .branch 166974846 d354 d369
private def d321 : MobiusHarmonicTree := .branch 278560511 d322 d353
private def d257 : MobiusHarmonicTree := .branch 525958177 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241664 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241728 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 26095698 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241792 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241856 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 21541973 d393 d394
private def d388 : MobiusHarmonicTree := .branch 47637671 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241920 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 241984 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 21811519 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242048 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242112 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 21019258 d400 d401
private def d395 : MobiusHarmonicTree := .branch 42830777 d396 d399
private def d387 : MobiusHarmonicTree := .branch 90468448 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242176 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242240 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 21990712 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242304 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242368 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 17184738 d408 d409
private def d403 : MobiusHarmonicTree := .branch 39175450 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242432 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242496 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 21818865 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242560 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242624 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 22623541 d415 d416
private def d410 : MobiusHarmonicTree := .branch 44442406 d411 d414
private def d402 : MobiusHarmonicTree := .branch 83617856 d403 d410
private def d386 : MobiusHarmonicTree := .branch 174086304 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242688 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242752 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 18727117 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242816 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242880 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 17465813 d424 d425
private def d419 : MobiusHarmonicTree := .branch 36192930 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 242944 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243008 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 9378877 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243072 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243136 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 3216388 d431 d432
private def d426 : MobiusHarmonicTree := .branch 12595265 d427 d430
private def d418 : MobiusHarmonicTree := .branch 48788195 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243200 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243264 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 1858073 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243328 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243392 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 5144010 d439 d440
private def d434 : MobiusHarmonicTree := .branch 7002083 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243456 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243520 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 2915857 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243584 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243648 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 2630894 d446 d447
private def d441 : MobiusHarmonicTree := .branch 5546751 d442 d445
private def d433 : MobiusHarmonicTree := .branch 12548834 d434 d441
private def d417 : MobiusHarmonicTree := .branch 61337029 d418 d433
private def d385 : MobiusHarmonicTree := .branch 235423333 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243712 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243776 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 2551631 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243840 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243904 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 1677067 d456 d457
private def d451 : MobiusHarmonicTree := .branch 4228698 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 243968 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244032 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 3028200 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244096 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244160 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 4927444 d463 d464
private def d458 : MobiusHarmonicTree := .branch 7955644 d459 d462
private def d450 : MobiusHarmonicTree := .branch 12184342 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244224 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244288 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 2816299 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244352 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244416 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 3616896 d471 d472
private def d466 : MobiusHarmonicTree := .branch 6433195 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244480 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244544 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 3005409 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244608 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244672 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 2975577 d478 d479
private def d473 : MobiusHarmonicTree := .branch 5980986 d474 d477
private def d465 : MobiusHarmonicTree := .branch 12414181 d466 d473
private def d449 : MobiusHarmonicTree := .branch 24598523 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244736 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244800 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 9060197 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244864 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244928 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 10574917 d487 d488
private def d482 : MobiusHarmonicTree := .branch 19635114 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 244992 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245056 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 5656051 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245120 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245184 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 3238548 d494 d495
private def d489 : MobiusHarmonicTree := .branch 8894599 d490 d493
private def d481 : MobiusHarmonicTree := .branch 28529713 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245248 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245312 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 4382046 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245376 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245440 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 7264337 d502 d503
private def d497 : MobiusHarmonicTree := .branch 11646383 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245504 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245568 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 9072978 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245632 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock029 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245696 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 13850339 d509 d510
private def d504 : MobiusHarmonicTree := .branch 22923317 d505 d508
private def d496 : MobiusHarmonicTree := .branch 34569700 d497 d504
private def d480 : MobiusHarmonicTree := .branch 63099413 d481 d496
private def d448 : MobiusHarmonicTree := .branch 87697936 d449 d480
private def d384 : MobiusHarmonicTree := .branch 323121269 d385 d448
private def d256 : MobiusHarmonicTree := .branch 849079446 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3910707266 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 229376 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 229376 3910707266 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 229376 3061627820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 229376 2099876031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 229376 1161657419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 229376 544175618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 229376 241061585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 229376 112329184 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 229376 55801086 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 229504 56528098 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 229632 128732401 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 229632 61054426 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 229760 67677975 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 229888 303114033 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 229888 145083806 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 229888 69679683 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230016 75404123 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 230144 158030227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230144 78329202 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230272 79701025 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 230400 617481801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 230400 314985472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 230400 157583575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230400 80551122 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230528 77032453 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 230656 157401897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230656 76963592 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230784 80438305 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 230912 302496329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 230912 160072502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 230912 79939130 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231040 80133372 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 231168 142423827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231168 70570372 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231296 71853455 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 231424 938218612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 231424 526240794 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 231424 272993463 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 231424 141874440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231424 72017407 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231552 69857033 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 231680 131119023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231680 67834330 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231808 63284693 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 231936 253247331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 231936 131745333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 231936 67780499 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232064 63964834 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 232192 121501998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232192 62160465 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232320 59341533 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 232448 411977818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 232448 227368217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 232448 117425712 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232448 61025147 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232576 56400565 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 232704 109942505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232704 55020793 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232832 54921712 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 232960 184609601 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 232960 100406260 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 232960 52759018 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233088 47647242 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 233216 84203341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233216 43518865 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233344 40684476 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 233472 961751789 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 233472 593346661 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 233472 299671958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 233472 161183660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 233472 80123593 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233472 38876359 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233600 41247234 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 233728 81060067 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233728 42431070 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233856 38628997 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 233984 138488298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 233984 65158575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 233984 34895035 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 234112 30263540 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 234240 73329723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 234240 37459688 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 234368 35870035 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 234496 293674703 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 234496 140422654 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 234496 65776734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 234496 30943163 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 234624 34833571 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 234752 74645920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 234752 36215671 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 234880 38430249 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 235008 153252049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 235008 81575002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235008 41630056 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235136 39944946 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 235264 71677047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235264 36604456 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235392 35072591 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 235520 368405128 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 235520 197591394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 235520 97732215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 235520 56943572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235520 31734349 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235648 25209223 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 235776 40788643 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235776 21171331 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 235904 19617312 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 236032 99859179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 236032 48672956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236032 21609759 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236160 27063197 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 236288 51186223 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236288 26477638 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236416 24708585 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 236544 170813734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 236544 81635833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 236544 39070451 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236544 18820273 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236672 20250178 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 236800 42565382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236800 20986655 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 236928 21578727 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 237056 89177901 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 237056 46150721 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237056 23924891 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237184 22225830 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 237312 43027180 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237312 23974568 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237440 19052612 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 237568 849079446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 237568 525958177 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 237568 247397666 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 237568 113720804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 237568 46840693 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 237568 23597450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237568 11282435 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237696 12315015 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 237824 23243243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237824 10113948 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 237952 13129295 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 238080 66880111 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 238080 29205271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238080 13731303 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238208 15473968 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 238336 37674840 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238336 19207270 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238464 18467570 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 238592 133676862 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 238592 72440743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 238592 37042909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238592 17334569 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238720 19708340 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 238848 35397834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238848 19040691 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 238976 16357143 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 239104 61236119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 239104 28449198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 239104 14090419 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 239232 14358779 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 239360 32786921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 239360 16978280 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 239488 15808641 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 239616 278560511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 239616 111585665 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 239616 54117669 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 239616 24565253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 239616 13739558 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 239744 10825695 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 239872 29552416 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 239872 12061436 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240000 17490980 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 240128 57467996 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 240128 31612505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240128 16083071 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240256 15529434 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 240384 25855491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240384 15916483 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240512 9939008 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 240640 166974846 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 240640 70847700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 240640 24404729 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240640 11462052 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240768 12942677 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 240896 46442971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 240896 22227831 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241024 24215140 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 241152 96127146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 241152 46817959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241152 24646253 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241280 22171706 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 241408 49309187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241408 24122967 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241536 25186220 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 241664 323121269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 241664 235423333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 241664 174086304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 241664 90468448 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 241664 47637671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241664 26095698 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241792 21541973 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 241920 42830777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 241920 21811519 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242048 21019258 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 242176 83617856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 242176 39175450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242176 21990712 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242304 17184738 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 242432 44442406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242432 21818865 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242560 22623541 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 242688 61337029 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 242688 48788195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 242688 36192930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242688 18727117 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242816 17465813 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 242944 12595265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 242944 9378877 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243072 3216388 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 243200 12548834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 243200 7002083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243200 1858073 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243328 5144010 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 243456 5546751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243456 2915857 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243584 2630894 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 243712 87697936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 243712 24598523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 243712 12184342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 243712 4228698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243712 2551631 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243840 1677067 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 243968 7955644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 243968 3028200 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244096 4927444 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 244224 12414181 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 244224 6433195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244224 2816299 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244352 3616896 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 244480 5980986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244480 3005409 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244608 2975577 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 244736 63099413 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 244736 28529713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 244736 19635114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244736 9060197 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244864 10574917 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 244992 8894599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 244992 5656051 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 245120 3238548 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 245248 34569700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 245248 11646383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 245248 4382046 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 245376 7264337 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 245504 22923317 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 245504 9072978 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 245632 13850339 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 229376 (MobiusHarmonicTree.branch 3910707266 mobiusHarmonicBlock028 mobiusHarmonicBlock029) = true := Helfgott.combined

#print axioms solution
