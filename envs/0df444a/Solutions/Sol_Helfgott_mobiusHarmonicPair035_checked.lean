-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair035_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:04:27.887731+00:00
-- url     : https://prove2.me/submissions/7a5ece4d-753d-480c-84f6-8f2d29d6f701

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573440 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573504 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 10053992 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573568 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573632 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 9534042 d11 d12
private def d6 : MobiusHarmonicTree := .branch 19588034 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573696 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573760 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 8259629 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573824 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573888 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 11314079 d18 d19
private def d13 : MobiusHarmonicTree := .branch 19573708 d14 d17
private def d5 : MobiusHarmonicTree := .branch 39161742 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573952 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574016 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 11628721 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574080 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574144 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 10119501 d26 d27
private def d21 : MobiusHarmonicTree := .branch 21748222 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574208 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574272 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 9845555 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574336 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574400 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 9066945 d33 d34
private def d28 : MobiusHarmonicTree := .branch 18912500 d29 d32
private def d20 : MobiusHarmonicTree := .branch 40660722 d21 d28
private def d4 : MobiusHarmonicTree := .branch 79822464 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574464 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574528 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 7494925 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574592 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574656 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 6410867 d42 d43
private def d37 : MobiusHarmonicTree := .branch 13905792 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574720 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574784 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 7340226 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574848 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574912 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 8347338 d49 d50
private def d44 : MobiusHarmonicTree := .branch 15687564 d45 d48
private def d36 : MobiusHarmonicTree := .branch 29593356 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 574976 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575040 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 9571597 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575104 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575168 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 9414700 d57 d58
private def d52 : MobiusHarmonicTree := .branch 18986297 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575232 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575296 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 10787546 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575360 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575424 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 8897879 d64 d65
private def d59 : MobiusHarmonicTree := .branch 19685425 d60 d63
private def d51 : MobiusHarmonicTree := .branch 38671722 d52 d59
private def d35 : MobiusHarmonicTree := .branch 68265078 d36 d51
private def d3 : MobiusHarmonicTree := .branch 148087542 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575488 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575552 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 10527286 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575616 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575680 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 13493665 d74 d75
private def d69 : MobiusHarmonicTree := .branch 24020951 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575744 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575808 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 13332657 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575872 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 575936 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 15281243 d81 d82
private def d76 : MobiusHarmonicTree := .branch 28613900 d77 d80
private def d68 : MobiusHarmonicTree := .branch 52634851 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576000 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576064 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 17527659 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576128 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576192 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 15604273 d89 d90
private def d84 : MobiusHarmonicTree := .branch 33131932 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576256 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576320 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 15829801 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576384 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576448 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 16591346 d96 d97
private def d91 : MobiusHarmonicTree := .branch 32421147 d92 d95
private def d83 : MobiusHarmonicTree := .branch 65553079 d84 d91
private def d67 : MobiusHarmonicTree := .branch 118187930 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576512 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576576 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 16946717 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576640 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576704 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 14811852 d105 d106
private def d100 : MobiusHarmonicTree := .branch 31758569 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576768 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576832 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 12251515 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576896 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576960 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 11364825 d112 d113
private def d107 : MobiusHarmonicTree := .branch 23616340 d108 d111
private def d99 : MobiusHarmonicTree := .branch 55374909 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577024 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577088 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 11859583 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577152 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577216 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 15082725 d120 d121
private def d115 : MobiusHarmonicTree := .branch 26942308 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577280 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577344 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 17395238 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577408 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577472 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 19098828 d127 d128
private def d122 : MobiusHarmonicTree := .branch 36494066 d123 d126
private def d114 : MobiusHarmonicTree := .branch 63436374 d115 d122
private def d98 : MobiusHarmonicTree := .branch 118811283 d99 d114
private def d66 : MobiusHarmonicTree := .branch 236999213 d67 d98
private def d2 : MobiusHarmonicTree := .branch 385086755 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577536 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577600 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 21158266 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577664 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577728 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 19760284 d138 d139
private def d133 : MobiusHarmonicTree := .branch 40918550 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577792 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577856 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 19252289 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577920 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 577984 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 18948726 d145 d146
private def d140 : MobiusHarmonicTree := .branch 38201015 d141 d144
private def d132 : MobiusHarmonicTree := .branch 79119565 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578048 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578112 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 19703866 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578176 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578240 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 18613528 d153 d154
private def d148 : MobiusHarmonicTree := .branch 38317394 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578304 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578368 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 15905211 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578432 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578496 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 15657885 d160 d161
private def d155 : MobiusHarmonicTree := .branch 31563096 d156 d159
private def d147 : MobiusHarmonicTree := .branch 69880490 d148 d155
private def d131 : MobiusHarmonicTree := .branch 149000055 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578560 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578624 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 16992101 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578688 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578752 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 16772393 d169 d170
private def d164 : MobiusHarmonicTree := .branch 33764494 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578816 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578880 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 17794785 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 578944 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579008 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 16182913 d176 d177
private def d171 : MobiusHarmonicTree := .branch 33977698 d172 d175
private def d163 : MobiusHarmonicTree := .branch 67742192 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579072 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579136 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 15806436 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579200 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579264 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 14590958 d184 d185
private def d179 : MobiusHarmonicTree := .branch 30397394 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579328 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579392 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 14662033 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579456 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579520 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 11965156 d191 d192
private def d186 : MobiusHarmonicTree := .branch 26627189 d187 d190
private def d178 : MobiusHarmonicTree := .branch 57024583 d179 d186
private def d162 : MobiusHarmonicTree := .branch 124766775 d163 d178
private def d130 : MobiusHarmonicTree := .branch 273766830 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579584 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579648 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 13616944 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579712 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579776 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 12675634 d201 d202
private def d196 : MobiusHarmonicTree := .branch 26292578 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579840 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579904 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 12241801 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 579968 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580032 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 11647777 d208 d209
private def d203 : MobiusHarmonicTree := .branch 23889578 d204 d207
private def d195 : MobiusHarmonicTree := .branch 50182156 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580096 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580160 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 9256143 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580224 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580288 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 7525672 d216 d217
private def d211 : MobiusHarmonicTree := .branch 16781815 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580352 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580416 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 6340385 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580480 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580544 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 7234591 d223 d224
private def d218 : MobiusHarmonicTree := .branch 13574976 d219 d222
private def d210 : MobiusHarmonicTree := .branch 30356791 d211 d218
private def d194 : MobiusHarmonicTree := .branch 80538947 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580608 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580672 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 9552784 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580736 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580800 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 9628212 d232 d233
private def d227 : MobiusHarmonicTree := .branch 19180996 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580864 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580928 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 9345415 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 580992 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581056 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 9346874 d239 d240
private def d234 : MobiusHarmonicTree := .branch 18692289 d235 d238
private def d226 : MobiusHarmonicTree := .branch 37873285 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581120 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581184 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 11612499 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581248 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581312 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 13433450 d247 d248
private def d242 : MobiusHarmonicTree := .branch 25045949 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581376 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581440 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 13705720 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581504 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock070 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581568 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 14036237 d254 d255
private def d249 : MobiusHarmonicTree := .branch 27741957 d250 d253
private def d241 : MobiusHarmonicTree := .branch 52787906 d242 d249
private def d225 : MobiusHarmonicTree := .branch 90661191 d226 d241
private def d193 : MobiusHarmonicTree := .branch 171200138 d194 d225
private def d129 : MobiusHarmonicTree := .branch 444966968 d130 d193
private def d1 : MobiusHarmonicTree := .branch 830053723 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581632 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581696 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 15150549 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581760 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581824 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 15697307 d266 d267
private def d261 : MobiusHarmonicTree := .branch 30847856 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581888 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 581952 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 15064914 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582016 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582080 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 14891561 d273 d274
private def d268 : MobiusHarmonicTree := .branch 29956475 d269 d272
private def d260 : MobiusHarmonicTree := .branch 60804331 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582144 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582208 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 15461884 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582272 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582336 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 16147160 d281 d282
private def d276 : MobiusHarmonicTree := .branch 31609044 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582400 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582464 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 13987188 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582528 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582592 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 13136201 d288 d289
private def d283 : MobiusHarmonicTree := .branch 27123389 d284 d287
private def d275 : MobiusHarmonicTree := .branch 58732433 d276 d283
private def d259 : MobiusHarmonicTree := .branch 119536764 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582656 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582720 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 12266665 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582784 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582848 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 14274815 d297 d298
private def d292 : MobiusHarmonicTree := .branch 26541480 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582912 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 582976 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 15561546 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583040 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583104 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 16144709 d304 d305
private def d299 : MobiusHarmonicTree := .branch 31706255 d300 d303
private def d291 : MobiusHarmonicTree := .branch 58247735 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583168 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583232 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 16988140 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583296 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583360 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 18539213 d312 d313
private def d307 : MobiusHarmonicTree := .branch 35527353 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583424 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583488 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 17748519 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583552 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583616 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 18716110 d319 d320
private def d314 : MobiusHarmonicTree := .branch 36464629 d315 d318
private def d306 : MobiusHarmonicTree := .branch 71991982 d307 d314
private def d290 : MobiusHarmonicTree := .branch 130239717 d291 d306
private def d258 : MobiusHarmonicTree := .branch 249776481 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583680 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583744 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 20975003 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583808 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583872 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 24647499 d329 d330
private def d324 : MobiusHarmonicTree := .branch 45622502 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 583936 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584000 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 24811757 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584064 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584128 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 23147475 d336 d337
private def d331 : MobiusHarmonicTree := .branch 47959232 d332 d335
private def d323 : MobiusHarmonicTree := .branch 93581734 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584192 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584256 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 22854777 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584320 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584384 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 24008220 d344 d345
private def d339 : MobiusHarmonicTree := .branch 46862997 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584448 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584512 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 22068140 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584576 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584640 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 23358047 d351 d352
private def d346 : MobiusHarmonicTree := .branch 45426187 d347 d350
private def d338 : MobiusHarmonicTree := .branch 92289184 d339 d346
private def d322 : MobiusHarmonicTree := .branch 185870918 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584704 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584768 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 24151531 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584832 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584896 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 23154657 d360 d361
private def d355 : MobiusHarmonicTree := .branch 47306188 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 584960 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585024 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 23106736 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585088 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585152 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 23288093 d367 d368
private def d362 : MobiusHarmonicTree := .branch 46394829 d363 d366
private def d354 : MobiusHarmonicTree := .branch 93701017 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585216 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585280 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 20040098 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585344 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585408 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 18819475 d375 d376
private def d370 : MobiusHarmonicTree := .branch 38859573 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585472 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585536 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 17491746 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585600 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585664 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 17417865 d382 d383
private def d377 : MobiusHarmonicTree := .branch 34909611 d378 d381
private def d369 : MobiusHarmonicTree := .branch 73769184 d370 d377
private def d353 : MobiusHarmonicTree := .branch 167470201 d354 d369
private def d321 : MobiusHarmonicTree := .branch 353341119 d322 d353
private def d257 : MobiusHarmonicTree := .branch 603117600 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585728 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585792 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 19626511 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585856 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585920 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 20455096 d393 d394
private def d388 : MobiusHarmonicTree := .branch 40081607 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 585984 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586048 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 20163928 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586112 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586176 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 23010284 d400 d401
private def d395 : MobiusHarmonicTree := .branch 43174212 d396 d399
private def d387 : MobiusHarmonicTree := .branch 83255819 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586240 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586304 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 21384907 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586368 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586432 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 21612092 d408 d409
private def d403 : MobiusHarmonicTree := .branch 42996999 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586496 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586560 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 21484665 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586624 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586688 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 23927587 d415 d416
private def d410 : MobiusHarmonicTree := .branch 45412252 d411 d414
private def d402 : MobiusHarmonicTree := .branch 88409251 d403 d410
private def d386 : MobiusHarmonicTree := .branch 171665070 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586752 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586816 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 27005085 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586880 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 586944 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 28626312 d424 d425
private def d419 : MobiusHarmonicTree := .branch 55631397 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587008 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587072 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 30059376 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587136 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587200 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 30470148 d431 d432
private def d426 : MobiusHarmonicTree := .branch 60529524 d427 d430
private def d418 : MobiusHarmonicTree := .branch 116160921 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587264 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587328 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 30895955 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587392 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587456 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 31610955 d439 d440
private def d434 : MobiusHarmonicTree := .branch 62506910 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587520 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587584 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 31268806 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587648 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587712 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 33778486 d446 d447
private def d441 : MobiusHarmonicTree := .branch 65047292 d442 d445
private def d433 : MobiusHarmonicTree := .branch 127554202 d434 d441
private def d417 : MobiusHarmonicTree := .branch 243715123 d418 d433
private def d385 : MobiusHarmonicTree := .branch 415380193 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587776 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587840 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 34390373 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587904 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 587968 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 36194207 d456 d457
private def d451 : MobiusHarmonicTree := .branch 70584580 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588032 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588096 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 36143875 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588160 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588224 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 35952350 d463 d464
private def d458 : MobiusHarmonicTree := .branch 72096225 d459 d462
private def d450 : MobiusHarmonicTree := .branch 142680805 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588288 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588352 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 36712812 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588416 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588480 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 35595239 d471 d472
private def d466 : MobiusHarmonicTree := .branch 72308051 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588544 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588608 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 32879378 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588672 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588736 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 33692567 d478 d479
private def d473 : MobiusHarmonicTree := .branch 66571945 d474 d477
private def d465 : MobiusHarmonicTree := .branch 138879996 d466 d473
private def d449 : MobiusHarmonicTree := .branch 281560801 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588800 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588864 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 33160550 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588928 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 588992 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 34992077 d487 d488
private def d482 : MobiusHarmonicTree := .branch 68152627 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589056 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589120 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 34852060 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589184 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589248 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 39574219 d494 d495
private def d489 : MobiusHarmonicTree := .branch 74426279 d490 d493
private def d481 : MobiusHarmonicTree := .branch 142578906 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589312 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589376 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 39284011 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589440 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589504 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 39107559 d502 d503
private def d497 : MobiusHarmonicTree := .branch 78391570 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589568 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589632 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 36029407 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589696 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock071 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589760 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 34141072 d509 d510
private def d504 : MobiusHarmonicTree := .branch 70170479 d505 d508
private def d496 : MobiusHarmonicTree := .branch 148562049 d497 d504
private def d480 : MobiusHarmonicTree := .branch 291140955 d481 d496
private def d448 : MobiusHarmonicTree := .branch 572701756 d449 d480
private def d384 : MobiusHarmonicTree := .branch 988081949 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1591199549 d257 d384
private def d0 : MobiusHarmonicTree := .branch 2421253272 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 573440 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 573440 2421253272 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 573440 830053723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 573440 385086755 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 573440 148087542 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 573440 79822464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 573440 39161742 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 573440 19588034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573440 10053992 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573568 9534042 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 573696 19573708 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573696 8259629 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573824 11314079 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 573952 40660722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 573952 21748222 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573952 11628721 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574080 10119501 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 574208 18912500 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574208 9845555 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574336 9066945 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 574464 68265078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 574464 29593356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 574464 13905792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574464 7494925 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574592 6410867 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 574720 15687564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574720 7340226 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574848 8347338 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 574976 38671722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 574976 18986297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 574976 9571597 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 575104 9414700 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 575232 19685425 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 575232 10787546 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 575360 8897879 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 575488 236999213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 575488 118187930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 575488 52634851 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 575488 24020951 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 575488 10527286 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 575616 13493665 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 575744 28613900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 575744 13332657 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 575872 15281243 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 576000 65553079 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 576000 33131932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576000 17527659 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576128 15604273 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 576256 32421147 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576256 15829801 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576384 16591346 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 576512 118811283 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 576512 55374909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 576512 31758569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576512 16946717 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576640 14811852 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 576768 23616340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576768 12251515 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 576896 11364825 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 577024 63436374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 577024 26942308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577024 11859583 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577152 15082725 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 577280 36494066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577280 17395238 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577408 19098828 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 577536 444966968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 577536 273766830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 577536 149000055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 577536 79119565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 577536 40918550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577536 21158266 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577664 19760284 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 577792 38201015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577792 19252289 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 577920 18948726 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 578048 69880490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 578048 38317394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578048 19703866 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578176 18613528 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 578304 31563096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578304 15905211 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578432 15657885 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 578560 124766775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 578560 67742192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 578560 33764494 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578560 16992101 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578688 16772393 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 578816 33977698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578816 17794785 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 578944 16182913 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 579072 57024583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 579072 30397394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579072 15806436 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579200 14590958 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 579328 26627189 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579328 14662033 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579456 11965156 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 579584 171200138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 579584 80538947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 579584 50182156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 579584 26292578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579584 13616944 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579712 12675634 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 579840 23889578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579840 12241801 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 579968 11647777 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 580096 30356791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 580096 16781815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580096 9256143 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580224 7525672 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 580352 13574976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580352 6340385 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580480 7234591 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 580608 90661191 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 580608 37873285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 580608 19180996 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580608 9552784 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580736 9628212 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 580864 18692289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580864 9345415 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 580992 9346874 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 581120 52787906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 581120 25045949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 581120 11612499 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 581248 13433450 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 581376 27741957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 581376 13705720 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 581504 14036237 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 581632 1591199549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 581632 603117600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 581632 249776481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 581632 119536764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 581632 60804331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 581632 30847856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 581632 15150549 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 581760 15697307 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 581888 29956475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 581888 15064914 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582016 14891561 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 582144 58732433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 582144 31609044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582144 15461884 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582272 16147160 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 582400 27123389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582400 13987188 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582528 13136201 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 582656 130239717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 582656 58247735 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 582656 26541480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582656 12266665 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582784 14274815 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 582912 31706255 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 582912 15561546 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583040 16144709 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 583168 71991982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 583168 35527353 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583168 16988140 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583296 18539213 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 583424 36464629 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583424 17748519 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583552 18716110 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 583680 353341119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 583680 185870918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 583680 93581734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 583680 45622502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583680 20975003 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583808 24647499 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 583936 47959232 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 583936 24811757 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584064 23147475 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 584192 92289184 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 584192 46862997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584192 22854777 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584320 24008220 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 584448 45426187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584448 22068140 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584576 23358047 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 584704 167470201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 584704 93701017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 584704 47306188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584704 24151531 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584832 23154657 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 584960 46394829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 584960 23106736 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585088 23288093 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 585216 73769184 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 585216 38859573 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585216 20040098 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585344 18819475 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 585472 34909611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585472 17491746 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585600 17417865 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 585728 988081949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 585728 415380193 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 585728 171665070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 585728 83255819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 585728 40081607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585728 19626511 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585856 20455096 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 585984 43174212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 585984 20163928 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 586112 23010284 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 586240 88409251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 586240 42996999 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 586240 21384907 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 586368 21612092 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 586496 45412252 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 586496 21484665 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 586624 23927587 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 586752 243715123 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 586752 116160921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 586752 55631397 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 586752 27005085 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 586880 28626312 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 587008 60529524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587008 30059376 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587136 30470148 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 587264 127554202 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 587264 62506910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587264 30895955 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587392 31610955 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 587520 65047292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587520 31268806 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587648 33778486 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 587776 572701756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 587776 281560801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 587776 142680805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 587776 70584580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587776 34390373 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 587904 36194207 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 588032 72096225 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588032 36143875 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588160 35952350 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 588288 138879996 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 588288 72308051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588288 36712812 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588416 35595239 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 588544 66571945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588544 32879378 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588672 33692567 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 588800 291140955 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 588800 142578906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 588800 68152627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588800 33160550 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 588928 34992077 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 589056 74426279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589056 34852060 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589184 39574219 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 589312 148562049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 589312 78391570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589312 39284011 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589440 39107559 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 589568 70170479 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589568 36029407 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589696 34141072 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 573440 (MobiusHarmonicTree.branch 2421253272 mobiusHarmonicBlock070 mobiusHarmonicBlock071) = true := Helfgott.combined

#print axioms solution
