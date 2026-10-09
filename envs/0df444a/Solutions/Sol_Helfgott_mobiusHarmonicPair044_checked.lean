-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair044_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:36:46.338296+00:00
-- url     : https://prove2.me/submissions/2690a00a-416e-493d-a35d-75ed66b7a060

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720896 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 720960 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 21201015 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721024 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721088 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 19638478 d11 d12
private def d6 : MobiusHarmonicTree := .branch 40839493 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721152 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721216 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 16201954 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721280 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721344 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 12400571 d18 d19
private def d13 : MobiusHarmonicTree := .branch 28602525 d14 d17
private def d5 : MobiusHarmonicTree := .branch 69442018 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721408 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721472 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 10398249 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721536 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721600 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 10863447 d26 d27
private def d21 : MobiusHarmonicTree := .branch 21261696 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721664 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721728 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 11026371 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721792 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721856 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 11794656 d33 d34
private def d28 : MobiusHarmonicTree := .branch 22821027 d29 d32
private def d20 : MobiusHarmonicTree := .branch 44082723 d21 d28
private def d4 : MobiusHarmonicTree := .branch 113524741 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721920 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 721984 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 13728873 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722048 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722112 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 15115456 d42 d43
private def d37 : MobiusHarmonicTree := .branch 28844329 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722176 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722240 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 15785678 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722304 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722368 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 12947832 d49 d50
private def d44 : MobiusHarmonicTree := .branch 28733510 d45 d48
private def d36 : MobiusHarmonicTree := .branch 57577839 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722432 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722496 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 11341327 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722560 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722624 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 12154339 d57 d58
private def d52 : MobiusHarmonicTree := .branch 23495666 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722688 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722752 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 16124535 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722816 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722880 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 16712382 d64 d65
private def d59 : MobiusHarmonicTree := .branch 32836917 d60 d63
private def d51 : MobiusHarmonicTree := .branch 56332583 d52 d59
private def d35 : MobiusHarmonicTree := .branch 113910422 d36 d51
private def d3 : MobiusHarmonicTree := .branch 227435163 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 722944 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723008 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 17589082 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723072 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723136 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 17143484 d74 d75
private def d69 : MobiusHarmonicTree := .branch 34732566 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723200 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723264 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 16222392 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723328 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723392 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 15821391 d81 d82
private def d76 : MobiusHarmonicTree := .branch 32043783 d77 d80
private def d68 : MobiusHarmonicTree := .branch 66776349 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723456 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723520 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 14736366 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723584 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723648 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 14033138 d89 d90
private def d84 : MobiusHarmonicTree := .branch 28769504 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723712 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723776 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 14203327 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723840 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723904 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 13954981 d96 d97
private def d91 : MobiusHarmonicTree := .branch 28158308 d92 d95
private def d83 : MobiusHarmonicTree := .branch 56927812 d84 d91
private def d67 : MobiusHarmonicTree := .branch 123704161 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 723968 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724032 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 13206672 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724096 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724160 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 12526306 d105 d106
private def d100 : MobiusHarmonicTree := .branch 25732978 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724224 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724288 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 12314221 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724352 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724416 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 13971313 d112 d113
private def d107 : MobiusHarmonicTree := .branch 26285534 d108 d111
private def d99 : MobiusHarmonicTree := .branch 52018512 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724480 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724544 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 12812276 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724608 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724672 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 11788848 d120 d121
private def d115 : MobiusHarmonicTree := .branch 24601124 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724736 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724800 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 9430276 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724864 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724928 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 11165280 d127 d128
private def d122 : MobiusHarmonicTree := .branch 20595556 d123 d126
private def d114 : MobiusHarmonicTree := .branch 45196680 d115 d122
private def d98 : MobiusHarmonicTree := .branch 97215192 d99 d114
private def d66 : MobiusHarmonicTree := .branch 220919353 d67 d98
private def d2 : MobiusHarmonicTree := .branch 448354516 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 724992 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725056 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 11087499 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725120 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725184 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 10939382 d138 d139
private def d133 : MobiusHarmonicTree := .branch 22026881 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725248 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725312 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 8262758 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725376 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725440 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 6294210 d145 d146
private def d140 : MobiusHarmonicTree := .branch 14556968 d141 d144
private def d132 : MobiusHarmonicTree := .branch 36583849 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725504 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725568 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 6315134 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725632 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725696 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 5327379 d153 d154
private def d148 : MobiusHarmonicTree := .branch 11642513 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725760 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725824 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 6081403 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725888 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 725952 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 8668675 d160 d161
private def d155 : MobiusHarmonicTree := .branch 14750078 d156 d159
private def d147 : MobiusHarmonicTree := .branch 26392591 d148 d155
private def d131 : MobiusHarmonicTree := .branch 62976440 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726016 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726080 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 9792368 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726144 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726208 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 7353359 d169 d170
private def d164 : MobiusHarmonicTree := .branch 17145727 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726272 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726336 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 8032158 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726400 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726464 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 6976349 d176 d177
private def d171 : MobiusHarmonicTree := .branch 15008507 d172 d175
private def d163 : MobiusHarmonicTree := .branch 32154234 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726528 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726592 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 5616742 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726656 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726720 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 4956564 d184 d185
private def d179 : MobiusHarmonicTree := .branch 10573306 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726784 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726848 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6137517 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726912 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 726976 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 5770577 d191 d192
private def d186 : MobiusHarmonicTree := .branch 11908094 d187 d190
private def d178 : MobiusHarmonicTree := .branch 22481400 d179 d186
private def d162 : MobiusHarmonicTree := .branch 54635634 d163 d178
private def d130 : MobiusHarmonicTree := .branch 117612074 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727040 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727104 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 5197377 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727168 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727232 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 6678820 d201 d202
private def d196 : MobiusHarmonicTree := .branch 11876197 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727296 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727360 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 7052932 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727424 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727488 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 8692995 d208 d209
private def d203 : MobiusHarmonicTree := .branch 15745927 d204 d207
private def d195 : MobiusHarmonicTree := .branch 27622124 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727552 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727616 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 7634644 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727680 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727744 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 6498217 d216 d217
private def d211 : MobiusHarmonicTree := .branch 14132861 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727808 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727872 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 6847446 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 727936 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728000 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 8390165 d223 d224
private def d218 : MobiusHarmonicTree := .branch 15237611 d219 d222
private def d210 : MobiusHarmonicTree := .branch 29370472 d211 d218
private def d194 : MobiusHarmonicTree := .branch 56992596 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728064 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728128 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 9171543 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728192 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728256 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 10694067 d232 d233
private def d227 : MobiusHarmonicTree := .branch 19865610 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728320 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728384 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 13572553 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728448 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728512 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 13935367 d239 d240
private def d234 : MobiusHarmonicTree := .branch 27507920 d235 d238
private def d226 : MobiusHarmonicTree := .branch 47373530 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728576 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728640 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 13337240 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728704 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728768 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 10937738 d247 d248
private def d242 : MobiusHarmonicTree := .branch 24274978 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728832 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728896 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 8345596 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 728960 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock088 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729024 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 5600724 d254 d255
private def d249 : MobiusHarmonicTree := .branch 13946320 d250 d253
private def d241 : MobiusHarmonicTree := .branch 38221298 d242 d249
private def d225 : MobiusHarmonicTree := .branch 85594828 d226 d241
private def d193 : MobiusHarmonicTree := .branch 142587424 d194 d225
private def d129 : MobiusHarmonicTree := .branch 260199498 d130 d193
private def d1 : MobiusHarmonicTree := .branch 708554014 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729088 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729152 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 7023287 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729216 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729280 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 8478274 d266 d267
private def d261 : MobiusHarmonicTree := .branch 15501561 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729344 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729408 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 7959959 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729472 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729536 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 7321200 d273 d274
private def d268 : MobiusHarmonicTree := .branch 15281159 d269 d272
private def d260 : MobiusHarmonicTree := .branch 30782720 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729600 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729664 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 3636020 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729728 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729792 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 3137948 d281 d282
private def d276 : MobiusHarmonicTree := .branch 6773968 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729856 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729920 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 2816801 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 729984 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730048 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 3580611 d288 d289
private def d283 : MobiusHarmonicTree := .branch 6397412 d284 d287
private def d275 : MobiusHarmonicTree := .branch 13171380 d276 d283
private def d259 : MobiusHarmonicTree := .branch 43954100 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730112 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730176 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 4997476 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730240 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730304 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 7659851 d297 d298
private def d292 : MobiusHarmonicTree := .branch 12657327 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730368 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730432 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 8126784 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730496 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730560 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 8772767 d304 d305
private def d299 : MobiusHarmonicTree := .branch 16899551 d300 d303
private def d291 : MobiusHarmonicTree := .branch 29556878 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730624 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730688 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 9565007 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730752 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730816 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 9077613 d312 d313
private def d307 : MobiusHarmonicTree := .branch 18642620 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730880 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 730944 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 9263401 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731008 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731072 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 10542110 d319 d320
private def d314 : MobiusHarmonicTree := .branch 19805511 d315 d318
private def d306 : MobiusHarmonicTree := .branch 38448131 d307 d314
private def d290 : MobiusHarmonicTree := .branch 68005009 d291 d306
private def d258 : MobiusHarmonicTree := .branch 111959109 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731136 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731200 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 11780731 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731264 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731328 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 9600441 d329 d330
private def d324 : MobiusHarmonicTree := .branch 21381172 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731392 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731456 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 9248753 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731520 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731584 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 9338708 d336 d337
private def d331 : MobiusHarmonicTree := .branch 18587461 d332 d335
private def d323 : MobiusHarmonicTree := .branch 39968633 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731648 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731712 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 8407785 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731776 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731840 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 5976787 d344 d345
private def d339 : MobiusHarmonicTree := .branch 14384572 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731904 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 731968 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 6518105 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732032 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732096 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 7403468 d351 d352
private def d346 : MobiusHarmonicTree := .branch 13921573 d347 d350
private def d338 : MobiusHarmonicTree := .branch 28306145 d339 d346
private def d322 : MobiusHarmonicTree := .branch 68274778 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732160 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732224 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 4926218 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732288 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732352 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 3432822 d360 d361
private def d355 : MobiusHarmonicTree := .branch 8359040 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732416 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732480 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 4942167 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732544 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732608 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 6794905 d367 d368
private def d362 : MobiusHarmonicTree := .branch 11737072 d363 d366
private def d354 : MobiusHarmonicTree := .branch 20096112 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732672 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732736 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 9586044 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732800 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732864 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 9813630 d375 d376
private def d370 : MobiusHarmonicTree := .branch 19399674 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732928 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 732992 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 10243031 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733056 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733120 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 10063942 d382 d383
private def d377 : MobiusHarmonicTree := .branch 20306973 d378 d381
private def d369 : MobiusHarmonicTree := .branch 39706647 d370 d377
private def d353 : MobiusHarmonicTree := .branch 59802759 d354 d369
private def d321 : MobiusHarmonicTree := .branch 128077537 d322 d353
private def d257 : MobiusHarmonicTree := .branch 240036646 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733184 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733248 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 9610731 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733312 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733376 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 8005515 d393 d394
private def d388 : MobiusHarmonicTree := .branch 17616246 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733440 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733504 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 9372870 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733568 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733632 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 10258636 d400 d401
private def d395 : MobiusHarmonicTree := .branch 19631506 d396 d399
private def d387 : MobiusHarmonicTree := .branch 37247752 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733696 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733760 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 10289530 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733824 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733888 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 8931980 d408 d409
private def d403 : MobiusHarmonicTree := .branch 19221510 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 733952 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734016 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 9348606 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734080 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734144 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 11499181 d415 d416
private def d410 : MobiusHarmonicTree := .branch 20847787 d411 d414
private def d402 : MobiusHarmonicTree := .branch 40069297 d403 d410
private def d386 : MobiusHarmonicTree := .branch 77317049 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734208 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734272 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 12879448 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734336 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734400 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 13020253 d424 d425
private def d419 : MobiusHarmonicTree := .branch 25899701 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734464 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734528 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 12591824 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734592 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734656 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 14212154 d431 d432
private def d426 : MobiusHarmonicTree := .branch 26803978 d427 d430
private def d418 : MobiusHarmonicTree := .branch 52703679 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734720 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734784 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 12587466 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734848 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734912 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 11431393 d439 d440
private def d434 : MobiusHarmonicTree := .branch 24018859 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 734976 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735040 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 10698811 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735104 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735168 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 9131340 d446 d447
private def d441 : MobiusHarmonicTree := .branch 19830151 d442 d445
private def d433 : MobiusHarmonicTree := .branch 43849010 d434 d441
private def d417 : MobiusHarmonicTree := .branch 96552689 d418 d433
private def d385 : MobiusHarmonicTree := .branch 173869738 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735232 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735296 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 8633344 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735360 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735424 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 8385692 d456 d457
private def d451 : MobiusHarmonicTree := .branch 17019036 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735488 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735552 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 9677130 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735616 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735680 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 8535087 d463 d464
private def d458 : MobiusHarmonicTree := .branch 18212217 d459 d462
private def d450 : MobiusHarmonicTree := .branch 35231253 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735744 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735808 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 8102700 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735872 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 735936 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 8235841 d471 d472
private def d466 : MobiusHarmonicTree := .branch 16338541 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736000 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736064 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 7283444 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736128 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736192 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 7426072 d478 d479
private def d473 : MobiusHarmonicTree := .branch 14709516 d474 d477
private def d465 : MobiusHarmonicTree := .branch 31048057 d466 d473
private def d449 : MobiusHarmonicTree := .branch 66279310 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736256 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736320 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 10287686 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736384 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736448 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 10011608 d487 d488
private def d482 : MobiusHarmonicTree := .branch 20299294 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736512 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736576 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 12358563 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736640 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736704 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 14649095 d494 d495
private def d489 : MobiusHarmonicTree := .branch 27007658 d490 d493
private def d481 : MobiusHarmonicTree := .branch 47306952 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736768 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736832 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 14584134 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736896 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 736960 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 15608778 d502 d503
private def d497 : MobiusHarmonicTree := .branch 30192912 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737024 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737088 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 15340208 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737152 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock089 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 737216 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 14801712 d509 d510
private def d504 : MobiusHarmonicTree := .branch 30141920 d505 d508
private def d496 : MobiusHarmonicTree := .branch 60334832 d497 d504
private def d480 : MobiusHarmonicTree := .branch 107641784 d481 d496
private def d448 : MobiusHarmonicTree := .branch 173921094 d449 d480
private def d384 : MobiusHarmonicTree := .branch 347790832 d385 d448
private def d256 : MobiusHarmonicTree := .branch 587827478 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1296381492 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 720896 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 720896 1296381492 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 720896 708554014 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 720896 448354516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 720896 227435163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 720896 113524741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 720896 69442018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 720896 40839493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 720896 21201015 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721024 19638478 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 721152 28602525 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721152 16201954 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721280 12400571 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 721408 44082723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 721408 21261696 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721408 10398249 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721536 10863447 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 721664 22821027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721664 11026371 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721792 11794656 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 721920 113910422 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 721920 57577839 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 721920 28844329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 721920 13728873 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722048 15115456 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 722176 28733510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722176 15785678 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722304 12947832 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 722432 56332583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 722432 23495666 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722432 11341327 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722560 12154339 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 722688 32836917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722688 16124535 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722816 16712382 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 722944 220919353 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 722944 123704161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 722944 66776349 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 722944 34732566 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 722944 17589082 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723072 17143484 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 723200 32043783 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723200 16222392 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723328 15821391 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 723456 56927812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 723456 28769504 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723456 14736366 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723584 14033138 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 723712 28158308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723712 14203327 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723840 13954981 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 723968 97215192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 723968 52018512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 723968 25732978 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 723968 13206672 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724096 12526306 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 724224 26285534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724224 12314221 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724352 13971313 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 724480 45196680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 724480 24601124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724480 12812276 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724608 11788848 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 724736 20595556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724736 9430276 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724864 11165280 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 724992 260199498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 724992 117612074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 724992 62976440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 724992 36583849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 724992 22026881 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 724992 11087499 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 725120 10939382 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 725248 14556968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 725248 8262758 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 725376 6294210 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 725504 26392591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 725504 11642513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 725504 6315134 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 725632 5327379 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 725760 14750078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 725760 6081403 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 725888 8668675 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 726016 54635634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 726016 32154234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 726016 17145727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726016 9792368 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726144 7353359 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 726272 15008507 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726272 8032158 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726400 6976349 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 726528 22481400 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 726528 10573306 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726528 5616742 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726656 4956564 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 726784 11908094 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726784 6137517 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 726912 5770577 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 727040 142587424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 727040 56992596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 727040 27622124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 727040 11876197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727040 5197377 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727168 6678820 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 727296 15745927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727296 7052932 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727424 8692995 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 727552 29370472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 727552 14132861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727552 7634644 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727680 6498217 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 727808 15237611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727808 6847446 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 727936 8390165 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 728064 85594828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 728064 47373530 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 728064 19865610 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728064 9171543 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728192 10694067 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 728320 27507920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728320 13572553 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728448 13935367 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 728576 38221298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 728576 24274978 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728576 13337240 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728704 10937738 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 728832 13946320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728832 8345596 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 728960 5600724 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 729088 587827478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 729088 240036646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 729088 111959109 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 729088 43954100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 729088 30782720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 729088 15501561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729088 7023287 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729216 8478274 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 729344 15281159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729344 7959959 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729472 7321200 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 729600 13171380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 729600 6773968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729600 3636020 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729728 3137948 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 729856 6397412 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729856 2816801 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 729984 3580611 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 730112 68005009 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 730112 29556878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 730112 12657327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 730112 4997476 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 730240 7659851 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 730368 16899551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 730368 8126784 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 730496 8772767 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 730624 38448131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 730624 18642620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 730624 9565007 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 730752 9077613 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 730880 19805511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 730880 9263401 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731008 10542110 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 731136 128077537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 731136 68274778 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 731136 39968633 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 731136 21381172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731136 11780731 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731264 9600441 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 731392 18587461 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731392 9248753 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731520 9338708 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 731648 28306145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 731648 14384572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731648 8407785 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731776 5976787 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 731904 13921573 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 731904 6518105 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732032 7403468 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 732160 59802759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 732160 20096112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 732160 8359040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732160 4926218 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732288 3432822 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 732416 11737072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732416 4942167 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732544 6794905 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 732672 39706647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 732672 19399674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732672 9586044 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732800 9813630 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 732928 20306973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 732928 10243031 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733056 10063942 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 733184 347790832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 733184 173869738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 733184 77317049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 733184 37247752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 733184 17616246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733184 9610731 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733312 8005515 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 733440 19631506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733440 9372870 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733568 10258636 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 733696 40069297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 733696 19221510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733696 10289530 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733824 8931980 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 733952 20847787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 733952 9348606 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734080 11499181 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 734208 96552689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 734208 52703679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 734208 25899701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734208 12879448 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734336 13020253 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 734464 26803978 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734464 12591824 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734592 14212154 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 734720 43849010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 734720 24018859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734720 12587466 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734848 11431393 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 734976 19830151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 734976 10698811 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 735104 9131340 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 735232 173921094 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 735232 66279310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 735232 35231253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 735232 17019036 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 735232 8633344 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 735360 8385692 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 735488 18212217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 735488 9677130 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 735616 8535087 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 735744 31048057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 735744 16338541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 735744 8102700 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 735872 8235841 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 736000 14709516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736000 7283444 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736128 7426072 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 736256 107641784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 736256 47306952 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 736256 20299294 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736256 10287686 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736384 10011608 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 736512 27007658 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736512 12358563 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736640 14649095 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 736768 60334832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 736768 30192912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736768 14584134 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 736896 15608778 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 737024 30141920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737024 15340208 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 737152 14801712 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 720896 (MobiusHarmonicTree.branch 1296381492 mobiusHarmonicBlock088 mobiusHarmonicBlock089) = true := Helfgott.combined

#print axioms solution
