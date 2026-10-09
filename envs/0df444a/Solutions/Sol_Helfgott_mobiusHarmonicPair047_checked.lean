-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair047_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:50:27.576981+00:00
-- url     : https://prove2.me/submissions/53310d8a-d382-4014-b7c4-a7625e94bae6

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770048 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770112 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 10214169 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770176 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770240 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 10379960 d11 d12
private def d6 : MobiusHarmonicTree := .branch 20594129 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770304 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770368 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 9239821 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770432 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770496 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 8811287 d18 d19
private def d13 : MobiusHarmonicTree := .branch 18051108 d14 d17
private def d5 : MobiusHarmonicTree := .branch 38645237 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770560 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770624 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 8755336 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770688 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770752 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 8727933 d26 d27
private def d21 : MobiusHarmonicTree := .branch 17483269 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770816 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770880 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 6797515 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 770944 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771008 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 5168657 d33 d34
private def d28 : MobiusHarmonicTree := .branch 11966172 d29 d32
private def d20 : MobiusHarmonicTree := .branch 29449441 d21 d28
private def d4 : MobiusHarmonicTree := .branch 68094678 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771072 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771136 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 4707404 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771200 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771264 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 5251195 d42 d43
private def d37 : MobiusHarmonicTree := .branch 9958599 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771328 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771392 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 4722721 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771456 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771520 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 4051784 d49 d50
private def d44 : MobiusHarmonicTree := .branch 8774505 d45 d48
private def d36 : MobiusHarmonicTree := .branch 18733104 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771584 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771648 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 5164339 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771712 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771776 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 6316645 d57 d58
private def d52 : MobiusHarmonicTree := .branch 11480984 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771840 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771904 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 7985517 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 771968 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772032 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 7330073 d64 d65
private def d59 : MobiusHarmonicTree := .branch 15315590 d60 d63
private def d51 : MobiusHarmonicTree := .branch 26796574 d52 d59
private def d35 : MobiusHarmonicTree := .branch 45529678 d36 d51
private def d3 : MobiusHarmonicTree := .branch 113624356 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772096 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772160 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 7119065 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772224 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772288 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 8024251 d74 d75
private def d69 : MobiusHarmonicTree := .branch 15143316 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772352 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772416 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 7323857 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772480 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772544 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 8492763 d81 d82
private def d76 : MobiusHarmonicTree := .branch 15816620 d77 d80
private def d68 : MobiusHarmonicTree := .branch 30959936 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772608 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772672 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 8836967 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772736 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772800 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 8517138 d89 d90
private def d84 : MobiusHarmonicTree := .branch 17354105 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772864 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772928 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 7804193 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 772992 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773056 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 6972386 d96 d97
private def d91 : MobiusHarmonicTree := .branch 14776579 d92 d95
private def d83 : MobiusHarmonicTree := .branch 32130684 d84 d91
private def d67 : MobiusHarmonicTree := .branch 63090620 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773120 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773184 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 7440725 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773248 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773312 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 7658013 d105 d106
private def d100 : MobiusHarmonicTree := .branch 15098738 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773376 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773440 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 10031853 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773504 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773568 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 9498922 d112 d113
private def d107 : MobiusHarmonicTree := .branch 19530775 d108 d111
private def d99 : MobiusHarmonicTree := .branch 34629513 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773632 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773696 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 7796472 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773760 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773824 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 5856697 d120 d121
private def d115 : MobiusHarmonicTree := .branch 13653169 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773888 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 773952 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 5778195 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774016 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774080 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 5994278 d127 d128
private def d122 : MobiusHarmonicTree := .branch 11772473 d123 d126
private def d114 : MobiusHarmonicTree := .branch 25425642 d115 d122
private def d98 : MobiusHarmonicTree := .branch 60055155 d99 d114
private def d66 : MobiusHarmonicTree := .branch 123145775 d67 d98
private def d2 : MobiusHarmonicTree := .branch 236770131 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774144 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774208 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 5821489 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774272 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774336 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 6550184 d138 d139
private def d133 : MobiusHarmonicTree := .branch 12371673 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774400 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774464 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 8726104 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774528 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774592 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 9303025 d145 d146
private def d140 : MobiusHarmonicTree := .branch 18029129 d141 d144
private def d132 : MobiusHarmonicTree := .branch 30400802 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774656 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774720 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 8332138 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774784 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774848 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 4644880 d153 d154
private def d148 : MobiusHarmonicTree := .branch 12977018 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774912 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 774976 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 4414344 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775040 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775104 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 4629144 d160 d161
private def d155 : MobiusHarmonicTree := .branch 9043488 d156 d159
private def d147 : MobiusHarmonicTree := .branch 22020506 d148 d155
private def d131 : MobiusHarmonicTree := .branch 52421308 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775168 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775232 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 3853093 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775296 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775360 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 3772491 d169 d170
private def d164 : MobiusHarmonicTree := .branch 7625584 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775424 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775488 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 5663569 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775552 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775616 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 5590489 d176 d177
private def d171 : MobiusHarmonicTree := .branch 11254058 d172 d175
private def d163 : MobiusHarmonicTree := .branch 18879642 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775680 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775744 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 4386844 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775808 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775872 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 3585707 d184 d185
private def d179 : MobiusHarmonicTree := .branch 7972551 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 775936 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776000 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 4578640 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776064 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776128 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 4860087 d191 d192
private def d186 : MobiusHarmonicTree := .branch 9438727 d187 d190
private def d178 : MobiusHarmonicTree := .branch 17411278 d179 d186
private def d162 : MobiusHarmonicTree := .branch 36290920 d163 d178
private def d130 : MobiusHarmonicTree := .branch 88712228 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776192 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776256 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 5904046 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776320 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776384 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 8092665 d201 d202
private def d196 : MobiusHarmonicTree := .branch 13996711 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776448 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776512 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 10274217 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776576 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776640 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 10157901 d208 d209
private def d203 : MobiusHarmonicTree := .branch 20432118 d204 d207
private def d195 : MobiusHarmonicTree := .branch 34428829 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776704 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776768 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 10802522 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776832 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776896 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 10172616 d216 d217
private def d211 : MobiusHarmonicTree := .branch 20975138 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 776960 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777024 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 8644609 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777088 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777152 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 6567695 d223 d224
private def d218 : MobiusHarmonicTree := .branch 15212304 d219 d222
private def d210 : MobiusHarmonicTree := .branch 36187442 d211 d218
private def d194 : MobiusHarmonicTree := .branch 70616271 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777216 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777280 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 4344713 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777344 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777408 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 3936258 d232 d233
private def d227 : MobiusHarmonicTree := .branch 8280971 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777472 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777536 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 3019858 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777600 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777664 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 4543128 d239 d240
private def d234 : MobiusHarmonicTree := .branch 7562986 d235 d238
private def d226 : MobiusHarmonicTree := .branch 15843957 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777728 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777792 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 4879268 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777856 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777920 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 5108559 d247 d248
private def d242 : MobiusHarmonicTree := .branch 9987827 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 777984 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778048 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 5435482 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778112 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock094 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778176 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 3942619 d254 d255
private def d249 : MobiusHarmonicTree := .branch 9378101 d250 d253
private def d241 : MobiusHarmonicTree := .branch 19365928 d242 d249
private def d225 : MobiusHarmonicTree := .branch 35209885 d226 d241
private def d193 : MobiusHarmonicTree := .branch 105826156 d194 d225
private def d129 : MobiusHarmonicTree := .branch 194538384 d130 d193
private def d1 : MobiusHarmonicTree := .branch 431308515 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778240 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778304 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 4047300 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778368 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778432 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 3537962 d266 d267
private def d261 : MobiusHarmonicTree := .branch 7585262 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778496 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778560 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 3600318 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778624 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778688 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 1354946 d273 d274
private def d268 : MobiusHarmonicTree := .branch 4955264 d269 d272
private def d260 : MobiusHarmonicTree := .branch 12540526 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778752 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778816 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 956628 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778880 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 778944 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 733085 d281 d282
private def d276 : MobiusHarmonicTree := .branch 1689713 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779008 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779072 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 906299 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779136 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779200 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 278535 d288 d289
private def d283 : MobiusHarmonicTree := .branch 1184834 d284 d287
private def d275 : MobiusHarmonicTree := .branch 2874547 d276 d283
private def d259 : MobiusHarmonicTree := .branch 15415073 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779264 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779328 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 318291 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779392 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779456 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 2257993 d297 d298
private def d292 : MobiusHarmonicTree := .branch 2576284 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779520 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779584 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 2507857 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779648 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779712 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 528454 d304 d305
private def d299 : MobiusHarmonicTree := .branch 3036311 d300 d303
private def d291 : MobiusHarmonicTree := .branch 5612595 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779776 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779840 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 1831192 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779904 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 779968 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 2154017 d312 d313
private def d307 : MobiusHarmonicTree := .branch 3985209 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780032 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780096 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 1228127 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780160 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780224 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 672967 d319 d320
private def d314 : MobiusHarmonicTree := .branch 1901094 d315 d318
private def d306 : MobiusHarmonicTree := .branch 5886303 d307 d314
private def d290 : MobiusHarmonicTree := .branch 11498898 d291 d306
private def d258 : MobiusHarmonicTree := .branch 26913971 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780288 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780352 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 335799 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780416 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780480 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 722677 d329 d330
private def d324 : MobiusHarmonicTree := .branch 1058476 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780544 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780608 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 2945210 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780672 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780736 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 2637318 d336 d337
private def d331 : MobiusHarmonicTree := .branch 5582528 d332 d335
private def d323 : MobiusHarmonicTree := .branch 6641004 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780800 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780864 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 1699488 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780928 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 780992 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 1745279 d344 d345
private def d339 : MobiusHarmonicTree := .branch 3444767 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781056 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781120 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 2022799 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781184 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781248 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 1506628 d351 d352
private def d346 : MobiusHarmonicTree := .branch 3529427 d347 d350
private def d338 : MobiusHarmonicTree := .branch 6974194 d339 d346
private def d322 : MobiusHarmonicTree := .branch 13615198 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781312 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781376 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 2070780 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781440 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781504 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 1374365 d360 d361
private def d355 : MobiusHarmonicTree := .branch 3445145 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781568 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781632 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 538660 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781696 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781760 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 565432 d367 d368
private def d362 : MobiusHarmonicTree := .branch 1104092 d363 d366
private def d354 : MobiusHarmonicTree := .branch 4549237 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781824 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781888 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 464310 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 781952 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782016 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 1341463 d375 d376
private def d370 : MobiusHarmonicTree := .branch 1805773 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782080 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782144 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 2144147 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782208 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782272 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 4293974 d382 d383
private def d377 : MobiusHarmonicTree := .branch 6438121 d378 d381
private def d369 : MobiusHarmonicTree := .branch 8243894 d370 d377
private def d353 : MobiusHarmonicTree := .branch 12793131 d354 d369
private def d321 : MobiusHarmonicTree := .branch 26408329 d322 d353
private def d257 : MobiusHarmonicTree := .branch 53322300 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782336 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782400 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 4242147 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782464 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782528 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 4164768 d393 d394
private def d388 : MobiusHarmonicTree := .branch 8406915 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782592 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782656 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 3921313 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782720 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782784 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 4406152 d400 d401
private def d395 : MobiusHarmonicTree := .branch 8327465 d396 d399
private def d387 : MobiusHarmonicTree := .branch 16734380 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782848 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782912 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 3918783 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 782976 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783040 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 4453232 d408 d409
private def d403 : MobiusHarmonicTree := .branch 8372015 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783104 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783168 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 4832974 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783232 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783296 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 6085876 d415 d416
private def d410 : MobiusHarmonicTree := .branch 10918850 d411 d414
private def d402 : MobiusHarmonicTree := .branch 19290865 d403 d410
private def d386 : MobiusHarmonicTree := .branch 36025245 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783360 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783424 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 5560306 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783488 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783552 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 4517955 d424 d425
private def d419 : MobiusHarmonicTree := .branch 10078261 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783616 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783680 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 3950633 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783744 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783808 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 6079343 d431 d432
private def d426 : MobiusHarmonicTree := .branch 10029976 d427 d430
private def d418 : MobiusHarmonicTree := .branch 20108237 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783872 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 783936 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 5740359 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784000 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784064 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 4998374 d439 d440
private def d434 : MobiusHarmonicTree := .branch 10738733 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784128 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784192 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 5153138 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784256 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784320 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 5956829 d446 d447
private def d441 : MobiusHarmonicTree := .branch 11109967 d442 d445
private def d433 : MobiusHarmonicTree := .branch 21848700 d434 d441
private def d417 : MobiusHarmonicTree := .branch 41956937 d418 d433
private def d385 : MobiusHarmonicTree := .branch 77982182 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784384 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784448 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 5662654 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784512 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784576 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 3937266 d456 d457
private def d451 : MobiusHarmonicTree := .branch 9599920 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784640 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784704 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 2394616 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784768 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784832 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 669011 d463 d464
private def d458 : MobiusHarmonicTree := .branch 3063627 d459 d462
private def d450 : MobiusHarmonicTree := .branch 12663547 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784896 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 784960 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 823038 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785024 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785088 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 977019 d471 d472
private def d466 : MobiusHarmonicTree := .branch 1800057 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785152 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785216 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 548953 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785280 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785344 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 625272 d478 d479
private def d473 : MobiusHarmonicTree := .branch 1174225 d474 d477
private def d465 : MobiusHarmonicTree := .branch 2974282 d466 d473
private def d449 : MobiusHarmonicTree := .branch 15637829 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785408 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785472 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 664649 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785536 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785600 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 472293 d487 d488
private def d482 : MobiusHarmonicTree := .branch 1136942 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785664 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785728 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 759872 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785792 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785856 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 1688652 d494 d495
private def d489 : MobiusHarmonicTree := .branch 2448524 d490 d493
private def d481 : MobiusHarmonicTree := .branch 3585466 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785920 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 785984 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 1001362 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786048 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786112 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 1577407 d502 d503
private def d497 : MobiusHarmonicTree := .branch 2578769 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786176 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786240 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 3557500 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786304 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock095 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786368 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 4121519 d509 d510
private def d504 : MobiusHarmonicTree := .branch 7679019 d505 d508
private def d496 : MobiusHarmonicTree := .branch 10257788 d497 d504
private def d480 : MobiusHarmonicTree := .branch 13843254 d481 d496
private def d448 : MobiusHarmonicTree := .branch 29481083 d449 d480
private def d384 : MobiusHarmonicTree := .branch 107463265 d385 d448
private def d256 : MobiusHarmonicTree := .branch 160785565 d257 d384
private def d0 : MobiusHarmonicTree := .branch 592094080 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 770048 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 770048 592094080 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 770048 431308515 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 770048 236770131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 770048 113624356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 770048 68094678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 770048 38645237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 770048 20594129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770048 10214169 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770176 10379960 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 770304 18051108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770304 9239821 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770432 8811287 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 770560 29449441 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 770560 17483269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770560 8755336 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770688 8727933 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 770816 11966172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770816 6797515 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 770944 5168657 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 771072 45529678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 771072 18733104 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 771072 9958599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771072 4707404 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771200 5251195 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 771328 8774505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771328 4722721 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771456 4051784 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 771584 26796574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 771584 11480984 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771584 5164339 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771712 6316645 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 771840 15315590 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771840 7985517 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 771968 7330073 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 772096 123145775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 772096 63090620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 772096 30959936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 772096 15143316 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772096 7119065 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772224 8024251 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 772352 15816620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772352 7323857 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772480 8492763 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 772608 32130684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 772608 17354105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772608 8836967 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772736 8517138 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 772864 14776579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772864 7804193 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 772992 6972386 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 773120 60055155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 773120 34629513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 773120 15098738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 773120 7440725 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 773248 7658013 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 773376 19530775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 773376 10031853 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 773504 9498922 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 773632 25425642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 773632 13653169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 773632 7796472 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 773760 5856697 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 773888 11772473 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 773888 5778195 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774016 5994278 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 774144 194538384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 774144 88712228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 774144 52421308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 774144 30400802 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 774144 12371673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774144 5821489 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774272 6550184 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 774400 18029129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774400 8726104 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774528 9303025 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 774656 22020506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 774656 12977018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774656 8332138 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774784 4644880 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 774912 9043488 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 774912 4414344 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775040 4629144 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 775168 36290920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 775168 18879642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 775168 7625584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775168 3853093 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775296 3772491 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 775424 11254058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775424 5663569 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775552 5590489 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 775680 17411278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 775680 7972551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775680 4386844 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775808 3585707 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 775936 9438727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 775936 4578640 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776064 4860087 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 776192 105826156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 776192 70616271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 776192 34428829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 776192 13996711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776192 5904046 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776320 8092665 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 776448 20432118 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776448 10274217 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776576 10157901 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 776704 36187442 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 776704 20975138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776704 10802522 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776832 10172616 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 776960 15212304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 776960 8644609 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777088 6567695 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 777216 35209885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 777216 15843957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 777216 8280971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777216 4344713 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777344 3936258 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 777472 7562986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777472 3019858 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777600 4543128 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 777728 19365928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 777728 9987827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777728 4879268 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777856 5108559 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 777984 9378101 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 777984 5435482 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 778112 3942619 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 778240 160785565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 778240 53322300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 778240 26913971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 778240 15415073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 778240 12540526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 778240 7585262 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 778240 4047300 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 778368 3537962 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 778496 4955264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 778496 3600318 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 778624 1354946 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 778752 2874547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 778752 1689713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 778752 956628 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 778880 733085 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 779008 1184834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779008 906299 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779136 278535 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 779264 11498898 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 779264 5612595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 779264 2576284 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779264 318291 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779392 2257993 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 779520 3036311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779520 2507857 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779648 528454 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 779776 5886303 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 779776 3985209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779776 1831192 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 779904 2154017 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 780032 1901094 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780032 1228127 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780160 672967 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 780288 26408329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 780288 13615198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 780288 6641004 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 780288 1058476 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780288 335799 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780416 722677 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 780544 5582528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780544 2945210 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780672 2637318 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 780800 6974194 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 780800 3444767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780800 1699488 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 780928 1745279 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 781056 3529427 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781056 2022799 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781184 1506628 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 781312 12793131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 781312 4549237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 781312 3445145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781312 2070780 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781440 1374365 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 781568 1104092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781568 538660 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781696 565432 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 781824 8243894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 781824 1805773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781824 464310 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 781952 1341463 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 782080 6438121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782080 2144147 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782208 4293974 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 782336 107463265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 782336 77982182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 782336 36025245 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 782336 16734380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 782336 8406915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782336 4242147 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782464 4164768 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 782592 8327465 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782592 3921313 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782720 4406152 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 782848 19290865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 782848 8372015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782848 3918783 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 782976 4453232 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 783104 10918850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 783104 4832974 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 783232 6085876 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 783360 41956937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 783360 20108237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 783360 10078261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 783360 5560306 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 783488 4517955 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 783616 10029976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 783616 3950633 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 783744 6079343 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 783872 21848700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 783872 10738733 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 783872 5740359 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784000 4998374 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 784128 11109967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784128 5153138 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784256 5956829 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 784384 29481083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 784384 15637829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 784384 12663547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 784384 9599920 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784384 5662654 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784512 3937266 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 784640 3063627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784640 2394616 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784768 669011 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 784896 2974282 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 784896 1800057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 784896 823038 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785024 977019 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 785152 1174225 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785152 548953 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785280 625272 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 785408 13843254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 785408 3585466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 785408 1136942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785408 664649 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785536 472293 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 785664 2448524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785664 759872 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785792 1688652 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 785920 10257788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 785920 2578769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 785920 1001362 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786048 1577407 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 786176 7679019 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786176 3557500 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786304 4121519 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 770048 (MobiusHarmonicTree.branch 592094080 mobiusHarmonicBlock094 mobiusHarmonicBlock095) = true := Helfgott.combined

#print axioms solution
