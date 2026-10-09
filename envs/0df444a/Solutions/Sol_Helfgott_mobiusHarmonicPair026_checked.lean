-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair026_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:28:15.109583+00:00
-- url     : https://prove2.me/submissions/7ce8ef00-f086-4246-99ba-ae71a6a13d34

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 425984 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426048 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 36770593 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426112 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426176 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 38737533 d11 d12
private def d6 : MobiusHarmonicTree := .branch 75508126 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426240 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426304 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 43438427 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426368 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426432 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 45775246 d18 d19
private def d13 : MobiusHarmonicTree := .branch 89213673 d14 d17
private def d5 : MobiusHarmonicTree := .branch 164721799 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426496 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426560 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 48992079 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426624 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426688 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 49952313 d26 d27
private def d21 : MobiusHarmonicTree := .branch 98944392 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426752 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426816 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 47563978 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426880 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 426944 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 42581848 d33 d34
private def d28 : MobiusHarmonicTree := .branch 90145826 d29 d32
private def d20 : MobiusHarmonicTree := .branch 189090218 d21 d28
private def d4 : MobiusHarmonicTree := .branch 353812017 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427008 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427072 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 40398486 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427136 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427200 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 41271185 d42 d43
private def d37 : MobiusHarmonicTree := .branch 81669671 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427264 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427328 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 41366424 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427392 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427456 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 37688293 d49 d50
private def d44 : MobiusHarmonicTree := .branch 79054717 d45 d48
private def d36 : MobiusHarmonicTree := .branch 160724388 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427520 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427584 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 33902216 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427648 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427712 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 35556847 d57 d58
private def d52 : MobiusHarmonicTree := .branch 69459063 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427776 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427840 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 35356706 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427904 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 427968 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 36862718 d64 d65
private def d59 : MobiusHarmonicTree := .branch 72219424 d60 d63
private def d51 : MobiusHarmonicTree := .branch 141678487 d52 d59
private def d35 : MobiusHarmonicTree := .branch 302402875 d36 d51
private def d3 : MobiusHarmonicTree := .branch 656214892 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428032 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428096 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 34758627 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428160 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428224 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 33251446 d74 d75
private def d69 : MobiusHarmonicTree := .branch 68010073 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428288 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428352 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 32454815 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428416 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428480 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 32316703 d81 d82
private def d76 : MobiusHarmonicTree := .branch 64771518 d77 d80
private def d68 : MobiusHarmonicTree := .branch 132781591 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428544 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428608 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 30510459 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428672 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428736 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 31637232 d89 d90
private def d84 : MobiusHarmonicTree := .branch 62147691 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428800 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428864 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 28342543 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428928 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 428992 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 27501820 d96 d97
private def d91 : MobiusHarmonicTree := .branch 55844363 d92 d95
private def d83 : MobiusHarmonicTree := .branch 117992054 d84 d91
private def d67 : MobiusHarmonicTree := .branch 250773645 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429056 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429120 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 27230387 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429184 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429248 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 23907165 d105 d106
private def d100 : MobiusHarmonicTree := .branch 51137552 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429312 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429376 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 21105171 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429440 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429504 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 20577312 d112 d113
private def d107 : MobiusHarmonicTree := .branch 41682483 d108 d111
private def d99 : MobiusHarmonicTree := .branch 92820035 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429568 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429632 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 18664933 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429696 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429760 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 18649980 d120 d121
private def d115 : MobiusHarmonicTree := .branch 37314913 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429824 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429888 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 19347045 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 429952 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430016 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 14406677 d127 d128
private def d122 : MobiusHarmonicTree := .branch 33753722 d123 d126
private def d114 : MobiusHarmonicTree := .branch 71068635 d115 d122
private def d98 : MobiusHarmonicTree := .branch 163888670 d99 d114
private def d66 : MobiusHarmonicTree := .branch 414662315 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1070877207 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430080 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430144 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 13718740 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430208 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430272 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 13733251 d138 d139
private def d133 : MobiusHarmonicTree := .branch 27451991 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430336 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430400 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 17142111 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430464 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430528 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 22623369 d145 d146
private def d140 : MobiusHarmonicTree := .branch 39765480 d141 d144
private def d132 : MobiusHarmonicTree := .branch 67217471 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430592 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430656 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 23297076 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430720 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430784 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 22442964 d153 d154
private def d148 : MobiusHarmonicTree := .branch 45740040 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430848 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430912 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 19602697 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 430976 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431040 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 20239481 d160 d161
private def d155 : MobiusHarmonicTree := .branch 39842178 d156 d159
private def d147 : MobiusHarmonicTree := .branch 85582218 d148 d155
private def d131 : MobiusHarmonicTree := .branch 152799689 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431104 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431168 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 20368134 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431232 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431296 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 14737278 d169 d170
private def d164 : MobiusHarmonicTree := .branch 35105412 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431360 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431424 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 13128681 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431488 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431552 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 13504860 d176 d177
private def d171 : MobiusHarmonicTree := .branch 26633541 d172 d175
private def d163 : MobiusHarmonicTree := .branch 61738953 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431616 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431680 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 13945539 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431744 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431808 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 13614955 d184 d185
private def d179 : MobiusHarmonicTree := .branch 27560494 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431872 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 431936 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 12337570 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432000 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432064 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 11188289 d191 d192
private def d186 : MobiusHarmonicTree := .branch 23525859 d187 d190
private def d178 : MobiusHarmonicTree := .branch 51086353 d179 d186
private def d162 : MobiusHarmonicTree := .branch 112825306 d163 d178
private def d130 : MobiusHarmonicTree := .branch 265624995 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432128 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432192 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 8741589 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432256 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432320 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 6539287 d201 d202
private def d196 : MobiusHarmonicTree := .branch 15280876 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432384 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432448 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 3080194 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432512 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432576 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 2984613 d208 d209
private def d203 : MobiusHarmonicTree := .branch 6064807 d204 d207
private def d195 : MobiusHarmonicTree := .branch 21345683 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432640 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432704 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 663321 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432768 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432832 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 2719308 d216 d217
private def d211 : MobiusHarmonicTree := .branch 3382629 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432896 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 432960 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 4764974 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433024 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433088 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 1706521 d223 d224
private def d218 : MobiusHarmonicTree := .branch 6471495 d219 d222
private def d210 : MobiusHarmonicTree := .branch 9854124 d211 d218
private def d194 : MobiusHarmonicTree := .branch 31199807 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433152 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433216 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 2735335 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433280 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433344 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 3770715 d232 d233
private def d227 : MobiusHarmonicTree := .branch 6506050 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433408 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433472 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 4067212 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433536 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433600 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 2128773 d239 d240
private def d234 : MobiusHarmonicTree := .branch 6195985 d235 d238
private def d226 : MobiusHarmonicTree := .branch 12702035 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433664 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433728 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 3854955 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433792 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433856 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 5568771 d247 d248
private def d242 : MobiusHarmonicTree := .branch 9423726 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433920 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 433984 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 4060180 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434048 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock052 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434112 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 1617183 d254 d255
private def d249 : MobiusHarmonicTree := .branch 5677363 d250 d253
private def d241 : MobiusHarmonicTree := .branch 15101089 d242 d249
private def d225 : MobiusHarmonicTree := .branch 27803124 d226 d241
private def d193 : MobiusHarmonicTree := .branch 59002931 d194 d225
private def d129 : MobiusHarmonicTree := .branch 324627926 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1395505133 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434176 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434240 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 2915463 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434304 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434368 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 4003561 d266 d267
private def d261 : MobiusHarmonicTree := .branch 6919024 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434432 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434496 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 6239455 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434560 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434624 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 7095928 d273 d274
private def d268 : MobiusHarmonicTree := .branch 13335383 d269 d272
private def d260 : MobiusHarmonicTree := .branch 20254407 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434688 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434752 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 3661967 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434816 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434880 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 5429156 d281 d282
private def d276 : MobiusHarmonicTree := .branch 9091123 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 434944 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435008 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 5873464 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435072 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435136 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 5299499 d288 d289
private def d283 : MobiusHarmonicTree := .branch 11172963 d284 d287
private def d275 : MobiusHarmonicTree := .branch 20264086 d276 d283
private def d259 : MobiusHarmonicTree := .branch 40518493 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435200 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435264 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 10244234 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435328 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435392 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 13509692 d297 d298
private def d292 : MobiusHarmonicTree := .branch 23753926 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435456 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435520 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 13012192 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435584 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435648 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 12225465 d304 d305
private def d299 : MobiusHarmonicTree := .branch 25237657 d300 d303
private def d291 : MobiusHarmonicTree := .branch 48991583 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435712 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435776 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 16494721 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435840 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435904 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 19212979 d312 d313
private def d307 : MobiusHarmonicTree := .branch 35707700 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 435968 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436032 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 19993981 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436096 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436160 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 18786866 d319 d320
private def d314 : MobiusHarmonicTree := .branch 38780847 d315 d318
private def d306 : MobiusHarmonicTree := .branch 74488547 d307 d314
private def d290 : MobiusHarmonicTree := .branch 123480130 d291 d306
private def d258 : MobiusHarmonicTree := .branch 163998623 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436224 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436288 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 17059900 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436352 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436416 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 14477196 d329 d330
private def d324 : MobiusHarmonicTree := .branch 31537096 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436480 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436544 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 15260811 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436608 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436672 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 15178551 d336 d337
private def d331 : MobiusHarmonicTree := .branch 30439362 d332 d335
private def d323 : MobiusHarmonicTree := .branch 61976458 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436736 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436800 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 15277241 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436864 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436928 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 11709177 d344 d345
private def d339 : MobiusHarmonicTree := .branch 26986418 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 436992 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437056 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 11433392 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437120 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437184 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 13785999 d351 d352
private def d346 : MobiusHarmonicTree := .branch 25219391 d347 d350
private def d338 : MobiusHarmonicTree := .branch 52205809 d339 d346
private def d322 : MobiusHarmonicTree := .branch 114182267 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437248 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437312 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 13267475 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437376 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437440 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 12715020 d360 d361
private def d355 : MobiusHarmonicTree := .branch 25982495 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437504 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437568 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 13762481 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437632 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437696 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 15574772 d367 d368
private def d362 : MobiusHarmonicTree := .branch 29337253 d363 d366
private def d354 : MobiusHarmonicTree := .branch 55319748 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437760 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437824 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 15766716 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437888 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 437952 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 14892190 d375 d376
private def d370 : MobiusHarmonicTree := .branch 30658906 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438016 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438080 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 12018515 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438144 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438208 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 6675160 d382 d383
private def d377 : MobiusHarmonicTree := .branch 18693675 d378 d381
private def d369 : MobiusHarmonicTree := .branch 49352581 d370 d377
private def d353 : MobiusHarmonicTree := .branch 104672329 d354 d369
private def d321 : MobiusHarmonicTree := .branch 218854596 d322 d353
private def d257 : MobiusHarmonicTree := .branch 382853219 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438272 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438336 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 3803104 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438400 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438464 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 4137211 d393 d394
private def d388 : MobiusHarmonicTree := .branch 7940315 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438528 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438592 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 4724375 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438656 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438720 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 3457897 d400 d401
private def d395 : MobiusHarmonicTree := .branch 8182272 d396 d399
private def d387 : MobiusHarmonicTree := .branch 16122587 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438784 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438848 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 3185643 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438912 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 438976 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 2505942 d408 d409
private def d403 : MobiusHarmonicTree := .branch 5691585 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439040 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439104 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 908740 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439168 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439232 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 1707517 d415 d416
private def d410 : MobiusHarmonicTree := .branch 2616257 d411 d414
private def d402 : MobiusHarmonicTree := .branch 8307842 d403 d410
private def d386 : MobiusHarmonicTree := .branch 24430429 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439296 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439360 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 1484057 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439424 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439488 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 655344 d424 d425
private def d419 : MobiusHarmonicTree := .branch 2139401 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439552 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439616 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 1758355 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439680 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439744 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 570839 d431 d432
private def d426 : MobiusHarmonicTree := .branch 2329194 d427 d430
private def d418 : MobiusHarmonicTree := .branch 4468595 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439808 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439872 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 2002919 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 439936 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440000 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 1702257 d439 d440
private def d434 : MobiusHarmonicTree := .branch 3705176 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440064 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440128 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 5737014 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440192 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440256 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 1526453 d446 d447
private def d441 : MobiusHarmonicTree := .branch 7263467 d442 d445
private def d433 : MobiusHarmonicTree := .branch 10968643 d434 d441
private def d417 : MobiusHarmonicTree := .branch 15437238 d418 d433
private def d385 : MobiusHarmonicTree := .branch 39867667 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440320 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440384 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 917476 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440448 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440512 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 898988 d456 d457
private def d451 : MobiusHarmonicTree := .branch 1816464 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440576 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440640 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 635453 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440704 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440768 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 3194474 d463 d464
private def d458 : MobiusHarmonicTree := .branch 3829927 d459 d462
private def d450 : MobiusHarmonicTree := .branch 5646391 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440832 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440896 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 3257058 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 440960 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441024 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 4645943 d471 d472
private def d466 : MobiusHarmonicTree := .branch 7903001 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441088 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441152 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 6052478 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441216 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441280 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 3363038 d478 d479
private def d473 : MobiusHarmonicTree := .branch 9415516 d474 d477
private def d465 : MobiusHarmonicTree := .branch 17318517 d466 d473
private def d449 : MobiusHarmonicTree := .branch 22964908 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441344 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441408 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 6005817 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441472 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441536 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 7279116 d487 d488
private def d482 : MobiusHarmonicTree := .branch 13284933 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441600 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441664 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 7895265 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441728 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441792 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 4769370 d494 d495
private def d489 : MobiusHarmonicTree := .branch 12664635 d490 d493
private def d481 : MobiusHarmonicTree := .branch 25949568 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441856 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441920 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 1289952 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 441984 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442048 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 2599239 d502 d503
private def d497 : MobiusHarmonicTree := .branch 3889191 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442112 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442176 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 4762811 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442240 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock053 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442304 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 7465464 d509 d510
private def d504 : MobiusHarmonicTree := .branch 12228275 d505 d508
private def d496 : MobiusHarmonicTree := .branch 16117466 d497 d504
private def d480 : MobiusHarmonicTree := .branch 42067034 d481 d496
private def d448 : MobiusHarmonicTree := .branch 65031942 d449 d480
private def d384 : MobiusHarmonicTree := .branch 104899609 d385 d448
private def d256 : MobiusHarmonicTree := .branch 487752828 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1883257961 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 425984 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 425984 1883257961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 425984 1395505133 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 425984 1070877207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 425984 656214892 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 425984 353812017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 425984 164721799 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 425984 75508126 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 425984 36770593 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 426112 38737533 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 426240 89213673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 426240 43438427 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 426368 45775246 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 426496 189090218 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 426496 98944392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 426496 48992079 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 426624 49952313 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 426752 90145826 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 426752 47563978 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 426880 42581848 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 427008 302402875 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 427008 160724388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 427008 81669671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427008 40398486 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427136 41271185 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 427264 79054717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427264 41366424 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427392 37688293 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 427520 141678487 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 427520 69459063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427520 33902216 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427648 35556847 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 427776 72219424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427776 35356706 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 427904 36862718 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 428032 414662315 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 428032 250773645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 428032 132781591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 428032 68010073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428032 34758627 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428160 33251446 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 428288 64771518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428288 32454815 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428416 32316703 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 428544 117992054 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 428544 62147691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428544 30510459 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428672 31637232 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 428800 55844363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428800 28342543 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 428928 27501820 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 429056 163888670 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 429056 92820035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 429056 51137552 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429056 27230387 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429184 23907165 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 429312 41682483 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429312 21105171 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429440 20577312 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 429568 71068635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 429568 37314913 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429568 18664933 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429696 18649980 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 429824 33753722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429824 19347045 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 429952 14406677 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 430080 324627926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 430080 265624995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 430080 152799689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 430080 67217471 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 430080 27451991 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430080 13718740 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430208 13733251 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 430336 39765480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430336 17142111 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430464 22623369 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 430592 85582218 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 430592 45740040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430592 23297076 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430720 22442964 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 430848 39842178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430848 19602697 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 430976 20239481 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 431104 112825306 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 431104 61738953 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 431104 35105412 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 431104 20368134 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 431232 14737278 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 431360 26633541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 431360 13128681 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 431488 13504860 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 431616 51086353 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 431616 27560494 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 431616 13945539 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 431744 13614955 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 431872 23525859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 431872 12337570 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432000 11188289 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 432128 59002931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 432128 31199807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 432128 21345683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 432128 15280876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432128 8741589 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432256 6539287 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 432384 6064807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432384 3080194 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432512 2984613 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 432640 9854124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 432640 3382629 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432640 663321 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432768 2719308 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 432896 6471495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 432896 4764974 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433024 1706521 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 433152 27803124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 433152 12702035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 433152 6506050 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433152 2735335 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433280 3770715 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 433408 6195985 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433408 4067212 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433536 2128773 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 433664 15101089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 433664 9423726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433664 3854955 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433792 5568771 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 433920 5677363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 433920 4060180 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434048 1617183 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 434176 487752828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 434176 382853219 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 434176 163998623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 434176 40518493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 434176 20254407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 434176 6919024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434176 2915463 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434304 4003561 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 434432 13335383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434432 6239455 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434560 7095928 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 434688 20264086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 434688 9091123 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434688 3661967 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434816 5429156 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 434944 11172963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 434944 5873464 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435072 5299499 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 435200 123480130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 435200 48991583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 435200 23753926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435200 10244234 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435328 13509692 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 435456 25237657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435456 13012192 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435584 12225465 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 435712 74488547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 435712 35707700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435712 16494721 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435840 19212979 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 435968 38780847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 435968 19993981 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436096 18786866 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 436224 218854596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 436224 114182267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 436224 61976458 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 436224 31537096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436224 17059900 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436352 14477196 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 436480 30439362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436480 15260811 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436608 15178551 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 436736 52205809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 436736 26986418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436736 15277241 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436864 11709177 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 436992 25219391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 436992 11433392 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 437120 13785999 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 437248 104672329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 437248 55319748 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 437248 25982495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 437248 13267475 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 437376 12715020 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 437504 29337253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 437504 13762481 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 437632 15574772 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 437760 49352581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 437760 30658906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 437760 15766716 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 437888 14892190 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 438016 18693675 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438016 12018515 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438144 6675160 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 438272 104899609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 438272 39867667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 438272 24430429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 438272 16122587 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 438272 7940315 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438272 3803104 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438400 4137211 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 438528 8182272 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438528 4724375 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438656 3457897 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 438784 8307842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 438784 5691585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438784 3185643 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 438912 2505942 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 439040 2616257 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439040 908740 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439168 1707517 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 439296 15437238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 439296 4468595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 439296 2139401 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439296 1484057 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439424 655344 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 439552 2329194 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439552 1758355 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439680 570839 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 439808 10968643 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 439808 3705176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439808 2002919 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 439936 1702257 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 440064 7263467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440064 5737014 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440192 1526453 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 440320 65031942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 440320 22964908 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 440320 5646391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 440320 1816464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440320 917476 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440448 898988 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 440576 3829927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440576 635453 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440704 3194474 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 440832 17318517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 440832 7903001 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440832 3257058 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 440960 4645943 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 441088 9415516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441088 6052478 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441216 3363038 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 441344 42067034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 441344 25949568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 441344 13284933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441344 6005817 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441472 7279116 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 441600 12664635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441600 7895265 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441728 4769370 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 441856 16117466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 441856 3889191 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441856 1289952 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 441984 2599239 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 442112 12228275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 442112 4762811 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 442240 7465464 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 425984 (MobiusHarmonicTree.branch 1883257961 mobiusHarmonicBlock052 mobiusHarmonicBlock053) = true := Helfgott.combined

#print axioms solution
