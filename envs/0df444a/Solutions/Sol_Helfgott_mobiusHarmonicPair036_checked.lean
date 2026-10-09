-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair036_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:09:30.384165+00:00
-- url     : https://prove2.me/submissions/3f48d92b-1a9c-49db-bb44-ff3931d0b7b0

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589824 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589888 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 35071187 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 589952 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590016 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 33082289 d11 d12
private def d6 : MobiusHarmonicTree := .branch 68153476 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590080 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590144 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 32359982 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590208 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590272 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 33210201 d18 d19
private def d13 : MobiusHarmonicTree := .branch 65570183 d14 d17
private def d5 : MobiusHarmonicTree := .branch 133723659 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590336 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590400 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 33709488 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590464 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590528 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 32174674 d26 d27
private def d21 : MobiusHarmonicTree := .branch 65884162 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590592 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590656 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 31327999 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590720 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590784 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 30782858 d33 d34
private def d28 : MobiusHarmonicTree := .branch 62110857 d29 d32
private def d20 : MobiusHarmonicTree := .branch 127995019 d21 d28
private def d4 : MobiusHarmonicTree := .branch 261718678 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590848 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590912 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 31556378 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 590976 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591040 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 31730599 d42 d43
private def d37 : MobiusHarmonicTree := .branch 63286977 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591104 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591168 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 32667610 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591232 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591296 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 32036509 d49 d50
private def d44 : MobiusHarmonicTree := .branch 64704119 d45 d48
private def d36 : MobiusHarmonicTree := .branch 127991096 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591360 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591424 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 31199357 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591488 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591552 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 30734516 d57 d58
private def d52 : MobiusHarmonicTree := .branch 61933873 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591616 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591680 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 30979714 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591744 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591808 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 29144693 d64 d65
private def d59 : MobiusHarmonicTree := .branch 60124407 d60 d63
private def d51 : MobiusHarmonicTree := .branch 122058280 d52 d59
private def d35 : MobiusHarmonicTree := .branch 250049376 d36 d51
private def d3 : MobiusHarmonicTree := .branch 511768054 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591872 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 591936 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 29180643 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592000 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592064 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 26829977 d74 d75
private def d69 : MobiusHarmonicTree := .branch 56010620 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592128 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592192 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 28229080 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592256 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592320 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 28915193 d81 d82
private def d76 : MobiusHarmonicTree := .branch 57144273 d77 d80
private def d68 : MobiusHarmonicTree := .branch 113154893 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592384 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592448 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 30639060 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592512 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592576 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 30737049 d89 d90
private def d84 : MobiusHarmonicTree := .branch 61376109 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592640 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592704 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 33249393 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592768 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592832 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 33144346 d96 d97
private def d91 : MobiusHarmonicTree := .branch 66393739 d92 d95
private def d83 : MobiusHarmonicTree := .branch 127769848 d84 d91
private def d67 : MobiusHarmonicTree := .branch 240924741 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592896 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 592960 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 33503244 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593024 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593088 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 31712089 d105 d106
private def d100 : MobiusHarmonicTree := .branch 65215333 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593152 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593216 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 31671491 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593280 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593344 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 31738855 d112 d113
private def d107 : MobiusHarmonicTree := .branch 63410346 d108 d111
private def d99 : MobiusHarmonicTree := .branch 128625679 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593408 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593472 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 33329340 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593536 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593600 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 36231489 d120 d121
private def d115 : MobiusHarmonicTree := .branch 69560829 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593664 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593728 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 36750934 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593792 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593856 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 36657128 d127 d128
private def d122 : MobiusHarmonicTree := .branch 73408062 d123 d126
private def d114 : MobiusHarmonicTree := .branch 142968891 d115 d122
private def d98 : MobiusHarmonicTree := .branch 271594570 d99 d114
private def d66 : MobiusHarmonicTree := .branch 512519311 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1024287365 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593920 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 593984 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 35213185 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594048 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594112 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 33268221 d138 d139
private def d133 : MobiusHarmonicTree := .branch 68481406 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594176 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594240 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 35886200 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594304 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594368 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 39445285 d145 d146
private def d140 : MobiusHarmonicTree := .branch 75331485 d141 d144
private def d132 : MobiusHarmonicTree := .branch 143812891 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594432 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594496 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 42639559 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594560 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594624 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 41715553 d153 d154
private def d148 : MobiusHarmonicTree := .branch 84355112 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594688 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594752 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 41829311 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594816 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594880 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 42084187 d160 d161
private def d155 : MobiusHarmonicTree := .branch 83913498 d156 d159
private def d147 : MobiusHarmonicTree := .branch 168268610 d148 d155
private def d131 : MobiusHarmonicTree := .branch 312081501 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 594944 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595008 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 44355733 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595072 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595136 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 48229374 d169 d170
private def d164 : MobiusHarmonicTree := .branch 92585107 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595200 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595264 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 49132942 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595328 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595392 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 48966163 d176 d177
private def d171 : MobiusHarmonicTree := .branch 98099105 d172 d175
private def d163 : MobiusHarmonicTree := .branch 190684212 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595456 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595520 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 49521446 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595584 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595648 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 49930653 d184 d185
private def d179 : MobiusHarmonicTree := .branch 99452099 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595712 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595776 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 48172633 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595840 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595904 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 45081224 d191 d192
private def d186 : MobiusHarmonicTree := .branch 93253857 d187 d190
private def d178 : MobiusHarmonicTree := .branch 192705956 d179 d186
private def d162 : MobiusHarmonicTree := .branch 383390168 d163 d178
private def d130 : MobiusHarmonicTree := .branch 695471669 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 595968 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596032 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 45157049 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596096 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596160 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 45462774 d201 d202
private def d196 : MobiusHarmonicTree := .branch 90619823 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596224 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596288 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 46883413 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596352 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596416 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 46828177 d208 d209
private def d203 : MobiusHarmonicTree := .branch 93711590 d204 d207
private def d195 : MobiusHarmonicTree := .branch 184331413 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596480 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596544 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 44829964 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596608 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596672 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 45720392 d216 d217
private def d211 : MobiusHarmonicTree := .branch 90550356 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596736 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596800 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 43961257 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596864 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596928 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 42507724 d223 d224
private def d218 : MobiusHarmonicTree := .branch 86468981 d219 d222
private def d210 : MobiusHarmonicTree := .branch 177019337 d211 d218
private def d194 : MobiusHarmonicTree := .branch 361350750 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 596992 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597056 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 43744756 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597120 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597184 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 44108750 d232 d233
private def d227 : MobiusHarmonicTree := .branch 87853506 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597248 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597312 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 46389550 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597376 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597440 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 48468569 d239 d240
private def d234 : MobiusHarmonicTree := .branch 94858119 d235 d238
private def d226 : MobiusHarmonicTree := .branch 182711625 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597504 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597568 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 48489940 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597632 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597696 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 51064470 d247 d248
private def d242 : MobiusHarmonicTree := .branch 99554410 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597760 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597824 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 52905299 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597888 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock072 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 597952 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 53541153 d254 d255
private def d249 : MobiusHarmonicTree := .branch 106446452 d250 d253
private def d241 : MobiusHarmonicTree := .branch 206000862 d242 d249
private def d225 : MobiusHarmonicTree := .branch 388712487 d226 d241
private def d193 : MobiusHarmonicTree := .branch 750063237 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1445534906 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2469822271 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598016 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598080 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 54270453 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598144 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598208 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 52593904 d266 d267
private def d261 : MobiusHarmonicTree := .branch 106864357 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598272 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598336 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 51103502 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598400 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598464 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 51781017 d273 d274
private def d268 : MobiusHarmonicTree := .branch 102884519 d269 d272
private def d260 : MobiusHarmonicTree := .branch 209748876 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598528 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598592 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 51926952 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598656 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598720 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 52158044 d281 d282
private def d276 : MobiusHarmonicTree := .branch 104084996 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598784 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598848 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 51236825 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598912 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 598976 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 51701651 d288 d289
private def d283 : MobiusHarmonicTree := .branch 102938476 d284 d287
private def d275 : MobiusHarmonicTree := .branch 207023472 d276 d283
private def d259 : MobiusHarmonicTree := .branch 416772348 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599040 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599104 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 51483694 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599168 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599232 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 48198501 d297 d298
private def d292 : MobiusHarmonicTree := .branch 99682195 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599296 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599360 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 49474576 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599424 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599488 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 48358029 d304 d305
private def d299 : MobiusHarmonicTree := .branch 97832605 d300 d303
private def d291 : MobiusHarmonicTree := .branch 197514800 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599552 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599616 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 49681919 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599680 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599744 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 48964341 d312 d313
private def d307 : MobiusHarmonicTree := .branch 98646260 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599808 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599872 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 48475446 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 599936 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600000 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 48326787 d319 d320
private def d314 : MobiusHarmonicTree := .branch 96802233 d315 d318
private def d306 : MobiusHarmonicTree := .branch 195448493 d307 d314
private def d290 : MobiusHarmonicTree := .branch 392963293 d291 d306
private def d258 : MobiusHarmonicTree := .branch 809735641 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600064 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600128 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 49307901 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600192 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600256 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 49452303 d329 d330
private def d324 : MobiusHarmonicTree := .branch 98760204 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600320 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600384 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 51262288 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600448 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600512 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 50766802 d336 d337
private def d331 : MobiusHarmonicTree := .branch 102029090 d332 d335
private def d323 : MobiusHarmonicTree := .branch 200789294 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600576 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600640 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 50812582 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600704 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600768 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 49971148 d344 d345
private def d339 : MobiusHarmonicTree := .branch 100783730 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600832 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600896 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 49724159 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 600960 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601024 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 50620351 d351 d352
private def d346 : MobiusHarmonicTree := .branch 100344510 d347 d350
private def d338 : MobiusHarmonicTree := .branch 201128240 d339 d346
private def d322 : MobiusHarmonicTree := .branch 401917534 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601088 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601152 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 51532854 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601216 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601280 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 51471919 d360 d361
private def d355 : MobiusHarmonicTree := .branch 103004773 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601344 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601408 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 52408783 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601472 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601536 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 50386158 d367 d368
private def d362 : MobiusHarmonicTree := .branch 102794941 d363 d366
private def d354 : MobiusHarmonicTree := .branch 205799714 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601600 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601664 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 49531075 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601728 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601792 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 49457380 d375 d376
private def d370 : MobiusHarmonicTree := .branch 98988455 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601856 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601920 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 49308999 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 601984 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602048 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 48125810 d382 d383
private def d377 : MobiusHarmonicTree := .branch 97434809 d378 d381
private def d369 : MobiusHarmonicTree := .branch 196423264 d370 d377
private def d353 : MobiusHarmonicTree := .branch 402222978 d354 d369
private def d321 : MobiusHarmonicTree := .branch 804140512 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1613876153 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602112 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602176 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 48098985 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602240 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602304 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 53125999 d393 d394
private def d388 : MobiusHarmonicTree := .branch 101224984 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602368 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602432 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 54590485 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602496 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602560 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 54716689 d400 d401
private def d395 : MobiusHarmonicTree := .branch 109307174 d396 d399
private def d387 : MobiusHarmonicTree := .branch 210532158 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602624 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602688 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 53906936 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602752 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602816 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 55964121 d408 d409
private def d403 : MobiusHarmonicTree := .branch 109871057 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602880 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 602944 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 57089990 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603008 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603072 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 57696342 d415 d416
private def d410 : MobiusHarmonicTree := .branch 114786332 d411 d414
private def d402 : MobiusHarmonicTree := .branch 224657389 d403 d410
private def d386 : MobiusHarmonicTree := .branch 435189547 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603136 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603200 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 57798544 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603264 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603328 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 54701752 d424 d425
private def d419 : MobiusHarmonicTree := .branch 112500296 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603392 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603456 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 52887127 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603520 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603584 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 54608903 d431 d432
private def d426 : MobiusHarmonicTree := .branch 107496030 d427 d430
private def d418 : MobiusHarmonicTree := .branch 219996326 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603648 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603712 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 53308683 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603776 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603840 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 53034022 d439 d440
private def d434 : MobiusHarmonicTree := .branch 106342705 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603904 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 603968 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 54393701 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604032 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604096 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 55193334 d446 d447
private def d441 : MobiusHarmonicTree := .branch 109587035 d442 d445
private def d433 : MobiusHarmonicTree := .branch 215929740 d434 d441
private def d417 : MobiusHarmonicTree := .branch 435926066 d418 d433
private def d385 : MobiusHarmonicTree := .branch 871115613 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604160 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604224 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 53940368 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604288 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604352 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 55156771 d456 d457
private def d451 : MobiusHarmonicTree := .branch 109097139 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604416 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604480 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 51704120 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604544 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604608 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 47756702 d463 d464
private def d458 : MobiusHarmonicTree := .branch 99460822 d459 d462
private def d450 : MobiusHarmonicTree := .branch 208557961 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604672 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604736 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 47440596 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604800 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604864 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 47204104 d471 d472
private def d466 : MobiusHarmonicTree := .branch 94644700 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604928 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 604992 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 47499910 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605056 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605120 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 46975904 d478 d479
private def d473 : MobiusHarmonicTree := .branch 94475814 d474 d477
private def d465 : MobiusHarmonicTree := .branch 189120514 d466 d473
private def d449 : MobiusHarmonicTree := .branch 397678475 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605184 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605248 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 46387723 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605312 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605376 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 44688008 d487 d488
private def d482 : MobiusHarmonicTree := .branch 91075731 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605440 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605504 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 44009751 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605568 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605632 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 45227236 d494 d495
private def d489 : MobiusHarmonicTree := .branch 89236987 d490 d493
private def d481 : MobiusHarmonicTree := .branch 180312718 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605696 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605760 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 42275995 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605824 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605888 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 38748185 d502 d503
private def d497 : MobiusHarmonicTree := .branch 81024180 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 605952 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606016 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 38739956 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606080 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock073 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606144 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 41561171 d509 d510
private def d504 : MobiusHarmonicTree := .branch 80301127 d505 d508
private def d496 : MobiusHarmonicTree := .branch 161325307 d497 d504
private def d480 : MobiusHarmonicTree := .branch 341638025 d481 d496
private def d448 : MobiusHarmonicTree := .branch 739316500 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1610432113 d385 d448
private def d256 : MobiusHarmonicTree := .branch 3224308266 d257 d384
private def d0 : MobiusHarmonicTree := .branch 5694130537 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 589824 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 589824 5694130537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 589824 2469822271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 589824 1024287365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 589824 511768054 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 589824 261718678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 589824 133723659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 589824 68153476 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589824 35071187 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 589952 33082289 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 590080 65570183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590080 32359982 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590208 33210201 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 590336 127995019 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 590336 65884162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590336 33709488 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590464 32174674 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 590592 62110857 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590592 31327999 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590720 30782858 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 590848 250049376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 590848 127991096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 590848 63286977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590848 31556378 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 590976 31730599 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 591104 64704119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 591104 32667610 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 591232 32036509 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 591360 122058280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 591360 61933873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 591360 31199357 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 591488 30734516 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 591616 60124407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 591616 30979714 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 591744 29144693 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 591872 512519311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 591872 240924741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 591872 113154893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 591872 56010620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 591872 29180643 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592000 26829977 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 592128 57144273 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592128 28229080 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592256 28915193 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 592384 127769848 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 592384 61376109 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592384 30639060 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592512 30737049 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 592640 66393739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592640 33249393 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592768 33144346 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 592896 271594570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 592896 128625679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 592896 65215333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 592896 33503244 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593024 31712089 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 593152 63410346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593152 31671491 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593280 31738855 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 593408 142968891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 593408 69560829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593408 33329340 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593536 36231489 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 593664 73408062 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593664 36750934 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593792 36657128 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 593920 1445534906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 593920 695471669 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 593920 312081501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 593920 143812891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 593920 68481406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 593920 35213185 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594048 33268221 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 594176 75331485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594176 35886200 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594304 39445285 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 594432 168268610 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 594432 84355112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594432 42639559 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594560 41715553 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 594688 83913498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594688 41829311 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594816 42084187 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 594944 383390168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 594944 190684212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 594944 92585107 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 594944 44355733 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595072 48229374 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 595200 98099105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595200 49132942 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595328 48966163 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 595456 192705956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 595456 99452099 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595456 49521446 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595584 49930653 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 595712 93253857 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595712 48172633 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595840 45081224 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 595968 750063237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 595968 361350750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 595968 184331413 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 595968 90619823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 595968 45157049 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596096 45462774 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 596224 93711590 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596224 46883413 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596352 46828177 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 596480 177019337 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 596480 90550356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596480 44829964 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596608 45720392 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 596736 86468981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596736 43961257 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596864 42507724 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 596992 388712487 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 596992 182711625 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 596992 87853506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 596992 43744756 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 597120 44108750 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 597248 94858119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 597248 46389550 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 597376 48468569 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 597504 206000862 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 597504 99554410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 597504 48489940 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 597632 51064470 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 597760 106446452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 597760 52905299 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 597888 53541153 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 598016 3224308266 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 598016 1613876153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 598016 809735641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 598016 416772348 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 598016 209748876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 598016 106864357 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598016 54270453 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598144 52593904 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 598272 102884519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598272 51103502 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598400 51781017 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 598528 207023472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 598528 104084996 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598528 51926952 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598656 52158044 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 598784 102938476 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598784 51236825 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 598912 51701651 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 599040 392963293 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 599040 197514800 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 599040 99682195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599040 51483694 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599168 48198501 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 599296 97832605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599296 49474576 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599424 48358029 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 599552 195448493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 599552 98646260 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599552 49681919 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599680 48964341 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 599808 96802233 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599808 48475446 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 599936 48326787 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 600064 804140512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 600064 401917534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 600064 200789294 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 600064 98760204 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600064 49307901 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600192 49452303 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 600320 102029090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600320 51262288 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600448 50766802 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 600576 201128240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 600576 100783730 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600576 50812582 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600704 49971148 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 600832 100344510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600832 49724159 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 600960 50620351 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 601088 402222978 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 601088 205799714 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 601088 103004773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601088 51532854 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601216 51471919 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 601344 102794941 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601344 52408783 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601472 50386158 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 601600 196423264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 601600 98988455 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601600 49531075 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601728 49457380 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 601856 97434809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601856 49308999 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 601984 48125810 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 602112 1610432113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 602112 871115613 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 602112 435189547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 602112 210532158 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 602112 101224984 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 602112 48098985 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 602240 53125999 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 602368 109307174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 602368 54590485 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 602496 54716689 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 602624 224657389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 602624 109871057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 602624 53906936 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 602752 55964121 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 602880 114786332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 602880 57089990 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603008 57696342 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 603136 435926066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 603136 219996326 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 603136 112500296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603136 57798544 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603264 54701752 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 603392 107496030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603392 52887127 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603520 54608903 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 603648 215929740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 603648 106342705 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603648 53308683 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603776 53034022 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 603904 109587035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 603904 54393701 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604032 55193334 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 604160 739316500 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 604160 397678475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 604160 208557961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 604160 109097139 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604160 53940368 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604288 55156771 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 604416 99460822 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604416 51704120 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604544 47756702 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 604672 189120514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 604672 94644700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604672 47440596 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604800 47204104 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 604928 94475814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 604928 47499910 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605056 46975904 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 605184 341638025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 605184 180312718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 605184 91075731 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605184 46387723 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605312 44688008 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 605440 89236987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605440 44009751 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605568 45227236 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 605696 161325307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 605696 81024180 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605696 42275995 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605824 38748185 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 605952 80301127 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 605952 38739956 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606080 41561171 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 589824 (MobiusHarmonicTree.branch 5694130537 mobiusHarmonicBlock072 mobiusHarmonicBlock073) = true := Helfgott.combined

#print axioms solution
