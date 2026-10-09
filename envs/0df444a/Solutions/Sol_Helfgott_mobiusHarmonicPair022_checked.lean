-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair022_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:12:07.620261+00:00
-- url     : https://prove2.me/submissions/fa545bb5-be14-4e87-915b-b1e7dbc17f86

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360448 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360512 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 55793077 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360576 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360640 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 52212958 d11 d12
private def d6 : MobiusHarmonicTree := .branch 108006035 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360704 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360768 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 45666691 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360832 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360896 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 47326738 d18 d19
private def d13 : MobiusHarmonicTree := .branch 92993429 d14 d17
private def d5 : MobiusHarmonicTree := .branch 200999464 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 360960 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361024 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 51395586 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361088 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361152 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 48461920 d26 d27
private def d21 : MobiusHarmonicTree := .branch 99857506 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361216 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361280 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 49083869 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361344 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361408 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 53745389 d33 d34
private def d28 : MobiusHarmonicTree := .branch 102829258 d29 d32
private def d20 : MobiusHarmonicTree := .branch 202686764 d21 d28
private def d4 : MobiusHarmonicTree := .branch 403686228 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361472 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361536 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 58494836 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361600 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361664 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 60340709 d42 d43
private def d37 : MobiusHarmonicTree := .branch 118835545 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361728 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361792 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 60825055 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361856 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361920 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 61657332 d49 d50
private def d44 : MobiusHarmonicTree := .branch 122482387 d45 d48
private def d36 : MobiusHarmonicTree := .branch 241317932 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 361984 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362048 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 62099801 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362112 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362176 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 59081926 d57 d58
private def d52 : MobiusHarmonicTree := .branch 121181727 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362240 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362304 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 59709615 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362368 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362432 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 61810358 d64 d65
private def d59 : MobiusHarmonicTree := .branch 121519973 d60 d63
private def d51 : MobiusHarmonicTree := .branch 242701700 d52 d59
private def d35 : MobiusHarmonicTree := .branch 484019632 d36 d51
private def d3 : MobiusHarmonicTree := .branch 887705860 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362496 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362560 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 59681373 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362624 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362688 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 54975793 d74 d75
private def d69 : MobiusHarmonicTree := .branch 114657166 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362752 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362816 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 51836552 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362880 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 362944 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 51082185 d81 d82
private def d76 : MobiusHarmonicTree := .branch 102918737 d77 d80
private def d68 : MobiusHarmonicTree := .branch 217575903 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363008 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363072 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 51389463 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363136 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363200 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 49934199 d89 d90
private def d84 : MobiusHarmonicTree := .branch 101323662 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363264 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363328 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 45011850 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363392 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363456 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 45028974 d96 d97
private def d91 : MobiusHarmonicTree := .branch 90040824 d92 d95
private def d83 : MobiusHarmonicTree := .branch 191364486 d84 d91
private def d67 : MobiusHarmonicTree := .branch 408940389 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363520 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363584 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 43780828 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363648 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363712 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 46237208 d105 d106
private def d100 : MobiusHarmonicTree := .branch 90018036 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363776 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363840 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 44137732 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363904 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 363968 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 44663444 d112 d113
private def d107 : MobiusHarmonicTree := .branch 88801176 d108 d111
private def d99 : MobiusHarmonicTree := .branch 178819212 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364032 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364096 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 42329673 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364160 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364224 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 44626496 d120 d121
private def d115 : MobiusHarmonicTree := .branch 86956169 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364288 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364352 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 43095966 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364416 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364480 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 40246585 d127 d128
private def d122 : MobiusHarmonicTree := .branch 83342551 d123 d126
private def d114 : MobiusHarmonicTree := .branch 170298720 d115 d122
private def d98 : MobiusHarmonicTree := .branch 349117932 d99 d114
private def d66 : MobiusHarmonicTree := .branch 758058321 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1645764181 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364544 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364608 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 41419869 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364672 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364736 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 41317778 d138 d139
private def d133 : MobiusHarmonicTree := .branch 82737647 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364800 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364864 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 36975581 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364928 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 364992 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 38444751 d145 d146
private def d140 : MobiusHarmonicTree := .branch 75420332 d141 d144
private def d132 : MobiusHarmonicTree := .branch 158157979 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365056 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365120 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 38015018 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365184 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365248 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 34357717 d153 d154
private def d148 : MobiusHarmonicTree := .branch 72372735 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365312 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365376 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 34288060 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365440 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365504 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 39465835 d160 d161
private def d155 : MobiusHarmonicTree := .branch 73753895 d156 d159
private def d147 : MobiusHarmonicTree := .branch 146126630 d148 d155
private def d131 : MobiusHarmonicTree := .branch 304284609 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365568 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365632 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 47195065 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365696 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365760 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 47566860 d169 d170
private def d164 : MobiusHarmonicTree := .branch 94761925 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365824 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365888 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 47760751 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 365952 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366016 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 46317727 d176 d177
private def d171 : MobiusHarmonicTree := .branch 94078478 d172 d175
private def d163 : MobiusHarmonicTree := .branch 188840403 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366080 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366144 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 46009351 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366208 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366272 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 49318469 d184 d185
private def d179 : MobiusHarmonicTree := .branch 95327820 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366336 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366400 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 54205842 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366464 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366528 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 53308603 d191 d192
private def d186 : MobiusHarmonicTree := .branch 107514445 d187 d190
private def d178 : MobiusHarmonicTree := .branch 202842265 d179 d186
private def d162 : MobiusHarmonicTree := .branch 391682668 d163 d178
private def d130 : MobiusHarmonicTree := .branch 695967277 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366592 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366656 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 45874428 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366720 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366784 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 44047916 d201 d202
private def d196 : MobiusHarmonicTree := .branch 89922344 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366848 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366912 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 43323961 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 366976 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367040 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 41238155 d208 d209
private def d203 : MobiusHarmonicTree := .branch 84562116 d204 d207
private def d195 : MobiusHarmonicTree := .branch 174484460 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367104 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367168 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 40766321 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367232 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367296 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 41059565 d216 d217
private def d211 : MobiusHarmonicTree := .branch 81825886 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367360 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367424 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 39836875 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367488 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367552 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 41939768 d223 d224
private def d218 : MobiusHarmonicTree := .branch 81776643 d219 d222
private def d210 : MobiusHarmonicTree := .branch 163602529 d211 d218
private def d194 : MobiusHarmonicTree := .branch 338086989 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367616 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367680 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 42433681 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367744 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367808 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 44893175 d232 d233
private def d227 : MobiusHarmonicTree := .branch 87326856 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367872 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 367936 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 43752453 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368000 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368064 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 40180645 d239 d240
private def d234 : MobiusHarmonicTree := .branch 83933098 d235 d238
private def d226 : MobiusHarmonicTree := .branch 171259954 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368128 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368192 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 40489872 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368256 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368320 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 41854946 d247 d248
private def d242 : MobiusHarmonicTree := .branch 82344818 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368384 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368448 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 41769770 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368512 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock044 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368576 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 43008998 d254 d255
private def d249 : MobiusHarmonicTree := .branch 84778768 d250 d253
private def d241 : MobiusHarmonicTree := .branch 167123586 d242 d249
private def d225 : MobiusHarmonicTree := .branch 338383540 d226 d241
private def d193 : MobiusHarmonicTree := .branch 676470529 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1372437806 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3018201987 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368640 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368704 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 40430873 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368768 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368832 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 44242503 d266 d267
private def d261 : MobiusHarmonicTree := .branch 84673376 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368896 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 368960 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 42416723 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369024 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369088 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 39668186 d273 d274
private def d268 : MobiusHarmonicTree := .branch 82084909 d269 d272
private def d260 : MobiusHarmonicTree := .branch 166758285 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369152 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369216 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 40087754 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369280 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369344 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 38953018 d281 d282
private def d276 : MobiusHarmonicTree := .branch 79040772 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369408 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369472 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 38289907 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369536 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369600 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 36867121 d288 d289
private def d283 : MobiusHarmonicTree := .branch 75157028 d284 d287
private def d275 : MobiusHarmonicTree := .branch 154197800 d276 d283
private def d259 : MobiusHarmonicTree := .branch 320956085 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369664 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369728 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 31012259 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369792 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369856 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 29157404 d297 d298
private def d292 : MobiusHarmonicTree := .branch 60169663 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369920 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 369984 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 30731073 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370048 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370112 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 31263629 d304 d305
private def d299 : MobiusHarmonicTree := .branch 61994702 d300 d303
private def d291 : MobiusHarmonicTree := .branch 122164365 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370176 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370240 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 29991478 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370304 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370368 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 25334426 d312 d313
private def d307 : MobiusHarmonicTree := .branch 55325904 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370432 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370496 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 24092117 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370560 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370624 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 24529165 d319 d320
private def d314 : MobiusHarmonicTree := .branch 48621282 d315 d318
private def d306 : MobiusHarmonicTree := .branch 103947186 d307 d314
private def d290 : MobiusHarmonicTree := .branch 226111551 d291 d306
private def d258 : MobiusHarmonicTree := .branch 547067636 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370688 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370752 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 22074272 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370816 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370880 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 19467273 d329 d330
private def d324 : MobiusHarmonicTree := .branch 41541545 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 370944 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371008 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 15719573 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371072 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371136 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 11834061 d336 d337
private def d331 : MobiusHarmonicTree := .branch 27553634 d332 d335
private def d323 : MobiusHarmonicTree := .branch 69095179 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371200 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371264 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 11089264 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371328 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371392 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 7870605 d344 d345
private def d339 : MobiusHarmonicTree := .branch 18959869 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371456 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371520 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 4600163 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371584 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371648 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 1585004 d351 d352
private def d346 : MobiusHarmonicTree := .branch 6185167 d347 d350
private def d338 : MobiusHarmonicTree := .branch 25145036 d339 d346
private def d322 : MobiusHarmonicTree := .branch 94240215 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371712 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371776 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 1783301 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371840 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371904 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 3939219 d360 d361
private def d355 : MobiusHarmonicTree := .branch 5722520 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 371968 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372032 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 2913800 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372096 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372160 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 2426510 d367 d368
private def d362 : MobiusHarmonicTree := .branch 5340310 d363 d366
private def d354 : MobiusHarmonicTree := .branch 11062830 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372224 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372288 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 2350497 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372352 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372416 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 3552507 d375 d376
private def d370 : MobiusHarmonicTree := .branch 5903004 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372480 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372544 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 6157584 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372608 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372672 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 6834675 d382 d383
private def d377 : MobiusHarmonicTree := .branch 12992259 d378 d381
private def d369 : MobiusHarmonicTree := .branch 18895263 d370 d377
private def d353 : MobiusHarmonicTree := .branch 29958093 d354 d369
private def d321 : MobiusHarmonicTree := .branch 124198308 d322 d353
private def d257 : MobiusHarmonicTree := .branch 671265944 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372736 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372800 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 1762495 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372864 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372928 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 1340722 d393 d394
private def d388 : MobiusHarmonicTree := .branch 3103217 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 372992 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373056 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 1174092 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373120 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373184 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 1886436 d400 d401
private def d395 : MobiusHarmonicTree := .branch 3060528 d396 d399
private def d387 : MobiusHarmonicTree := .branch 6163745 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373248 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373312 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 1473474 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373376 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373440 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 1740578 d408 d409
private def d403 : MobiusHarmonicTree := .branch 3214052 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373504 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373568 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 4307163 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373632 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373696 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 2643913 d415 d416
private def d410 : MobiusHarmonicTree := .branch 6951076 d411 d414
private def d402 : MobiusHarmonicTree := .branch 10165128 d403 d410
private def d386 : MobiusHarmonicTree := .branch 16328873 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373760 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373824 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 2677814 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373888 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 373952 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 4254606 d424 d425
private def d419 : MobiusHarmonicTree := .branch 6932420 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374016 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374080 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 3282923 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374144 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374208 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 2859367 d431 d432
private def d426 : MobiusHarmonicTree := .branch 6142290 d427 d430
private def d418 : MobiusHarmonicTree := .branch 13074710 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374272 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374336 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 8241227 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374400 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374464 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 11328222 d439 d440
private def d434 : MobiusHarmonicTree := .branch 19569449 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374528 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374592 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 9533147 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374656 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374720 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 9433771 d446 d447
private def d441 : MobiusHarmonicTree := .branch 18966918 d442 d445
private def d433 : MobiusHarmonicTree := .branch 38536367 d434 d441
private def d417 : MobiusHarmonicTree := .branch 51611077 d418 d433
private def d385 : MobiusHarmonicTree := .branch 67939950 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374784 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374848 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 8480876 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374912 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 374976 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 5797883 d456 d457
private def d451 : MobiusHarmonicTree := .branch 14278759 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375040 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375104 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 3916298 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375168 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375232 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 3827044 d463 d464
private def d458 : MobiusHarmonicTree := .branch 7743342 d459 d462
private def d450 : MobiusHarmonicTree := .branch 22022101 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375296 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375360 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 6055575 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375424 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375488 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 6090908 d471 d472
private def d466 : MobiusHarmonicTree := .branch 12146483 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375552 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375616 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 2872788 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375680 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375744 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 1389308 d478 d479
private def d473 : MobiusHarmonicTree := .branch 4262096 d474 d477
private def d465 : MobiusHarmonicTree := .branch 16408579 d466 d473
private def d449 : MobiusHarmonicTree := .branch 38430680 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375808 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375872 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 928596 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 375936 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376000 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 965483 d487 d488
private def d482 : MobiusHarmonicTree := .branch 1894079 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376064 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376128 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 2360895 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376192 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376256 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 4635223 d494 d495
private def d489 : MobiusHarmonicTree := .branch 6996118 d490 d493
private def d481 : MobiusHarmonicTree := .branch 8890197 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376320 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376384 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 2986425 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376448 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376512 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 2762308 d502 d503
private def d497 : MobiusHarmonicTree := .branch 5748733 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376576 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376640 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 2012578 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376704 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock045 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376768 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 2741779 d509 d510
private def d504 : MobiusHarmonicTree := .branch 4754357 d505 d508
private def d496 : MobiusHarmonicTree := .branch 10503090 d497 d504
private def d480 : MobiusHarmonicTree := .branch 19393287 d481 d496
private def d448 : MobiusHarmonicTree := .branch 57823967 d449 d480
private def d384 : MobiusHarmonicTree := .branch 125763917 d385 d448
private def d256 : MobiusHarmonicTree := .branch 797029861 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3815231848 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 360448 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 360448 3815231848 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 360448 3018201987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 360448 1645764181 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 360448 887705860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 360448 403686228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 360448 200999464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 360448 108006035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360448 55793077 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360576 52212958 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 360704 92993429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360704 45666691 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360832 47326738 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 360960 202686764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 360960 99857506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 360960 51395586 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361088 48461920 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 361216 102829258 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361216 49083869 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361344 53745389 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 361472 484019632 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 361472 241317932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 361472 118835545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361472 58494836 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361600 60340709 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 361728 122482387 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361728 60825055 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361856 61657332 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 361984 242701700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 361984 121181727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 361984 62099801 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 362112 59081926 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 362240 121519973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 362240 59709615 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 362368 61810358 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 362496 758058321 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 362496 408940389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 362496 217575903 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 362496 114657166 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 362496 59681373 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 362624 54975793 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 362752 102918737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 362752 51836552 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 362880 51082185 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 363008 191364486 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 363008 101323662 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363008 51389463 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363136 49934199 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 363264 90040824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363264 45011850 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363392 45028974 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 363520 349117932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 363520 178819212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 363520 90018036 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363520 43780828 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363648 46237208 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 363776 88801176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363776 44137732 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 363904 44663444 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 364032 170298720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 364032 86956169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364032 42329673 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364160 44626496 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 364288 83342551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364288 43095966 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364416 40246585 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 364544 1372437806 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 364544 695967277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 364544 304284609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 364544 158157979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 364544 82737647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364544 41419869 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364672 41317778 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 364800 75420332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364800 36975581 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 364928 38444751 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 365056 146126630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 365056 72372735 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365056 38015018 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365184 34357717 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 365312 73753895 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365312 34288060 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365440 39465835 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 365568 391682668 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 365568 188840403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 365568 94761925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365568 47195065 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365696 47566860 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 365824 94078478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365824 47760751 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 365952 46317727 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 366080 202842265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 366080 95327820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366080 46009351 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366208 49318469 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 366336 107514445 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366336 54205842 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366464 53308603 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 366592 676470529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 366592 338086989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 366592 174484460 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 366592 89922344 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366592 45874428 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366720 44047916 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 366848 84562116 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366848 43323961 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 366976 41238155 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 367104 163602529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 367104 81825886 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 367104 40766321 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 367232 41059565 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 367360 81776643 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 367360 39836875 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 367488 41939768 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 367616 338383540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 367616 171259954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 367616 87326856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 367616 42433681 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 367744 44893175 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 367872 83933098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 367872 43752453 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368000 40180645 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 368128 167123586 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 368128 82344818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368128 40489872 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368256 41854946 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 368384 84778768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368384 41769770 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368512 43008998 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 368640 797029861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 368640 671265944 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 368640 547067636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 368640 320956085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 368640 166758285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 368640 84673376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368640 40430873 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368768 44242503 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 368896 82084909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 368896 42416723 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369024 39668186 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 369152 154197800 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 369152 79040772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369152 40087754 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369280 38953018 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 369408 75157028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369408 38289907 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369536 36867121 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 369664 226111551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 369664 122164365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 369664 60169663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369664 31012259 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369792 29157404 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 369920 61994702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 369920 30731073 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370048 31263629 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 370176 103947186 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 370176 55325904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370176 29991478 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370304 25334426 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 370432 48621282 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370432 24092117 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370560 24529165 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 370688 124198308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 370688 94240215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 370688 69095179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 370688 41541545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370688 22074272 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370816 19467273 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 370944 27553634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 370944 15719573 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371072 11834061 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 371200 25145036 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 371200 18959869 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371200 11089264 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371328 7870605 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 371456 6185167 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371456 4600163 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371584 1585004 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 371712 29958093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 371712 11062830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 371712 5722520 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371712 1783301 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371840 3939219 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 371968 5340310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 371968 2913800 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372096 2426510 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 372224 18895263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 372224 5903004 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372224 2350497 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372352 3552507 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 372480 12992259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372480 6157584 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372608 6834675 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 372736 125763917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 372736 67939950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 372736 16328873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 372736 6163745 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 372736 3103217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372736 1762495 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372864 1340722 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 372992 3060528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 372992 1174092 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 373120 1886436 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 373248 10165128 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 373248 3214052 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 373248 1473474 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 373376 1740578 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 373504 6951076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 373504 4307163 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 373632 2643913 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 373760 51611077 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 373760 13074710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 373760 6932420 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 373760 2677814 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 373888 4254606 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 374016 6142290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374016 3282923 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374144 2859367 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 374272 38536367 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 374272 19569449 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374272 8241227 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374400 11328222 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 374528 18966918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374528 9533147 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374656 9433771 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 374784 57823967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 374784 38430680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 374784 22022101 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 374784 14278759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374784 8480876 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 374912 5797883 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 375040 7743342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375040 3916298 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375168 3827044 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 375296 16408579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 375296 12146483 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375296 6055575 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375424 6090908 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 375552 4262096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375552 2872788 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375680 1389308 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 375808 19393287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 375808 8890197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 375808 1894079 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375808 928596 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 375936 965483 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 376064 6996118 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376064 2360895 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376192 4635223 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 376320 10503090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 376320 5748733 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376320 2986425 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376448 2762308 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 376576 4754357 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376576 2012578 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376704 2741779 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 360448 (MobiusHarmonicTree.branch 3815231848 mobiusHarmonicBlock044 mobiusHarmonicBlock045) = true := Helfgott.combined

#print axioms solution
