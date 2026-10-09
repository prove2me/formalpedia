-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair028_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:36:05.81012+00:00
-- url     : https://prove2.me/submissions/54786527-8e89-4888-a5c4-b46ab9573468

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458752 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458816 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 36402465 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458880 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458944 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 34586095 d11 d12
private def d6 : MobiusHarmonicTree := .branch 70988560 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459008 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459072 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 35434573 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459136 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459200 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 37992198 d18 d19
private def d13 : MobiusHarmonicTree := .branch 73426771 d14 d17
private def d5 : MobiusHarmonicTree := .branch 144415331 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459264 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459328 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 39094214 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459392 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459456 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 40347796 d26 d27
private def d21 : MobiusHarmonicTree := .branch 79442010 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459520 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459584 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 41924915 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459648 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459712 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 41993755 d33 d34
private def d28 : MobiusHarmonicTree := .branch 83918670 d29 d32
private def d20 : MobiusHarmonicTree := .branch 163360680 d21 d28
private def d4 : MobiusHarmonicTree := .branch 307776011 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459776 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459840 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 43736970 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459904 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 459968 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 46838049 d42 d43
private def d37 : MobiusHarmonicTree := .branch 90575019 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460032 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460096 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 50107061 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460160 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460224 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 51288126 d49 d50
private def d44 : MobiusHarmonicTree := .branch 101395187 d45 d48
private def d36 : MobiusHarmonicTree := .branch 191970206 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460288 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460352 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 53409202 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460416 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460480 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 54858005 d57 d58
private def d52 : MobiusHarmonicTree := .branch 108267207 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460544 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460608 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 55765639 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460672 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460736 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 56609461 d64 d65
private def d59 : MobiusHarmonicTree := .branch 112375100 d60 d63
private def d51 : MobiusHarmonicTree := .branch 220642307 d52 d59
private def d35 : MobiusHarmonicTree := .branch 412612513 d36 d51
private def d3 : MobiusHarmonicTree := .branch 720388524 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460800 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460864 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 57472581 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460928 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 460992 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 56760449 d74 d75
private def d69 : MobiusHarmonicTree := .branch 114233030 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461056 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461120 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 54662618 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461184 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461248 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 56188989 d81 d82
private def d76 : MobiusHarmonicTree := .branch 110851607 d77 d80
private def d68 : MobiusHarmonicTree := .branch 225084637 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461312 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461376 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 54903318 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461440 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461504 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 53984454 d89 d90
private def d84 : MobiusHarmonicTree := .branch 108887772 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461568 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461632 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 55102465 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461696 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461760 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 56267335 d96 d97
private def d91 : MobiusHarmonicTree := .branch 111369800 d92 d95
private def d83 : MobiusHarmonicTree := .branch 220257572 d84 d91
private def d67 : MobiusHarmonicTree := .branch 445342209 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461824 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461888 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 57910234 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 461952 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462016 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 59480669 d105 d106
private def d100 : MobiusHarmonicTree := .branch 117390903 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462080 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462144 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 60704198 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462208 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462272 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 61768974 d112 d113
private def d107 : MobiusHarmonicTree := .branch 122473172 d108 d111
private def d99 : MobiusHarmonicTree := .branch 239864075 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462336 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462400 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 60145086 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462464 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462528 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 58604200 d120 d121
private def d115 : MobiusHarmonicTree := .branch 118749286 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462592 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462656 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 57371036 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462720 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462784 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 59565641 d127 d128
private def d122 : MobiusHarmonicTree := .branch 116936677 d123 d126
private def d114 : MobiusHarmonicTree := .branch 235685963 d115 d122
private def d98 : MobiusHarmonicTree := .branch 475550038 d99 d114
private def d66 : MobiusHarmonicTree := .branch 920892247 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1641280771 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462848 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462912 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 61193191 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 462976 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463040 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 63083208 d138 d139
private def d133 : MobiusHarmonicTree := .branch 124276399 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463104 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463168 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 65684726 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463232 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463296 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 65919130 d145 d146
private def d140 : MobiusHarmonicTree := .branch 131603856 d141 d144
private def d132 : MobiusHarmonicTree := .branch 255880255 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463360 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463424 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 64284776 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463488 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463552 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 60390380 d153 d154
private def d148 : MobiusHarmonicTree := .branch 124675156 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463616 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463680 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 59049476 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463744 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463808 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 60990797 d160 d161
private def d155 : MobiusHarmonicTree := .branch 120040273 d156 d159
private def d147 : MobiusHarmonicTree := .branch 244715429 d148 d155
private def d131 : MobiusHarmonicTree := .branch 500595684 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463872 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 463936 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 61318958 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464000 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464064 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 60405622 d169 d170
private def d164 : MobiusHarmonicTree := .branch 121724580 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464128 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464192 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 58460798 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464256 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464320 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 59896254 d176 d177
private def d171 : MobiusHarmonicTree := .branch 118357052 d172 d175
private def d163 : MobiusHarmonicTree := .branch 240081632 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464384 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464448 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 59320052 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464512 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464576 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 57984257 d184 d185
private def d179 : MobiusHarmonicTree := .branch 117304309 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464640 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464704 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 56930994 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464768 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464832 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 55418059 d191 d192
private def d186 : MobiusHarmonicTree := .branch 112349053 d187 d190
private def d178 : MobiusHarmonicTree := .branch 229653362 d179 d186
private def d162 : MobiusHarmonicTree := .branch 469734994 d163 d178
private def d130 : MobiusHarmonicTree := .branch 970330678 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464896 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 464960 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 53421989 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465024 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465088 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 50315459 d201 d202
private def d196 : MobiusHarmonicTree := .branch 103737448 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465152 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465216 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 46900849 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465280 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465344 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 45654543 d208 d209
private def d203 : MobiusHarmonicTree := .branch 92555392 d204 d207
private def d195 : MobiusHarmonicTree := .branch 196292840 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465408 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465472 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 45637652 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465536 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465600 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 45401701 d216 d217
private def d211 : MobiusHarmonicTree := .branch 91039353 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465664 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465728 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 48045312 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465792 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465856 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 50273140 d223 d224
private def d218 : MobiusHarmonicTree := .branch 98318452 d219 d222
private def d210 : MobiusHarmonicTree := .branch 189357805 d211 d218
private def d194 : MobiusHarmonicTree := .branch 385650645 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465920 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 465984 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 51079108 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466048 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466112 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 46386031 d232 d233
private def d227 : MobiusHarmonicTree := .branch 97465139 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466176 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466240 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 46085798 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466304 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466368 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 47050948 d239 d240
private def d234 : MobiusHarmonicTree := .branch 93136746 d235 d238
private def d226 : MobiusHarmonicTree := .branch 190601885 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466432 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466496 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 44836536 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466560 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466624 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 45715667 d247 d248
private def d242 : MobiusHarmonicTree := .branch 90552203 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466688 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466752 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 47457843 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466816 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock056 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466880 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 46373904 d254 d255
private def d249 : MobiusHarmonicTree := .branch 93831747 d250 d253
private def d241 : MobiusHarmonicTree := .branch 184383950 d242 d249
private def d225 : MobiusHarmonicTree := .branch 374985835 d226 d241
private def d193 : MobiusHarmonicTree := .branch 760636480 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1730967158 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3372247929 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 466944 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467008 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 47183469 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467072 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467136 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 46922212 d266 d267
private def d261 : MobiusHarmonicTree := .branch 94105681 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467200 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467264 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 46530542 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467328 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467392 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 46419421 d273 d274
private def d268 : MobiusHarmonicTree := .branch 92949963 d269 d272
private def d260 : MobiusHarmonicTree := .branch 187055644 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467456 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467520 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 45726483 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467584 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467648 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 45237125 d281 d282
private def d276 : MobiusHarmonicTree := .branch 90963608 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467712 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467776 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 41549994 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467840 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467904 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 40038297 d288 d289
private def d283 : MobiusHarmonicTree := .branch 81588291 d284 d287
private def d275 : MobiusHarmonicTree := .branch 172551899 d276 d283
private def d259 : MobiusHarmonicTree := .branch 359607543 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 467968 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468032 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 40826296 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468096 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468160 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 39546448 d297 d298
private def d292 : MobiusHarmonicTree := .branch 80372744 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468224 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468288 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 38269334 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468352 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468416 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 37964202 d304 d305
private def d299 : MobiusHarmonicTree := .branch 76233536 d300 d303
private def d291 : MobiusHarmonicTree := .branch 156606280 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468480 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468544 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 39021000 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468608 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468672 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 38521756 d312 d313
private def d307 : MobiusHarmonicTree := .branch 77542756 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468736 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468800 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 36245864 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468864 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468928 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 35001204 d319 d320
private def d314 : MobiusHarmonicTree := .branch 71247068 d315 d318
private def d306 : MobiusHarmonicTree := .branch 148789824 d307 d314
private def d290 : MobiusHarmonicTree := .branch 305396104 d291 d306
private def d258 : MobiusHarmonicTree := .branch 665003647 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 468992 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469056 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 34168696 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469120 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469184 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 33927133 d329 d330
private def d324 : MobiusHarmonicTree := .branch 68095829 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469248 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469312 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 33025073 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469376 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469440 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 30440600 d336 d337
private def d331 : MobiusHarmonicTree := .branch 63465673 d332 d335
private def d323 : MobiusHarmonicTree := .branch 131561502 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469504 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469568 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 32900565 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469632 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469696 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 32474294 d344 d345
private def d339 : MobiusHarmonicTree := .branch 65374859 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469760 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469824 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 32448431 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469888 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 469952 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 33018268 d351 d352
private def d346 : MobiusHarmonicTree := .branch 65466699 d347 d350
private def d338 : MobiusHarmonicTree := .branch 130841558 d339 d346
private def d322 : MobiusHarmonicTree := .branch 262403060 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470016 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470080 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 36670468 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470144 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470208 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 34801800 d360 d361
private def d355 : MobiusHarmonicTree := .branch 71472268 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470272 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470336 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 33465482 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470400 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470464 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 33692383 d367 d368
private def d362 : MobiusHarmonicTree := .branch 67157865 d363 d366
private def d354 : MobiusHarmonicTree := .branch 138630133 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470528 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470592 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 31938665 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470656 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470720 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 31186337 d375 d376
private def d370 : MobiusHarmonicTree := .branch 63125002 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470784 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470848 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 30402690 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470912 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 470976 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 27581146 d382 d383
private def d377 : MobiusHarmonicTree := .branch 57983836 d378 d381
private def d369 : MobiusHarmonicTree := .branch 121108838 d370 d377
private def d353 : MobiusHarmonicTree := .branch 259738971 d354 d369
private def d321 : MobiusHarmonicTree := .branch 522142031 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1187145678 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471040 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471104 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 28063969 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471168 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471232 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 28098855 d393 d394
private def d388 : MobiusHarmonicTree := .branch 56162824 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471296 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471360 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 25492264 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471424 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471488 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 23508725 d400 d401
private def d395 : MobiusHarmonicTree := .branch 49000989 d396 d399
private def d387 : MobiusHarmonicTree := .branch 105163813 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471552 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471616 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 23894442 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471680 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471744 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 24163579 d408 d409
private def d403 : MobiusHarmonicTree := .branch 48058021 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471808 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471872 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 25797294 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 471936 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472000 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 27605946 d415 d416
private def d410 : MobiusHarmonicTree := .branch 53403240 d411 d414
private def d402 : MobiusHarmonicTree := .branch 101461261 d403 d410
private def d386 : MobiusHarmonicTree := .branch 206625074 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472064 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472128 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 26139277 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472192 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472256 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 27690465 d424 d425
private def d419 : MobiusHarmonicTree := .branch 53829742 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472320 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472384 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 29514231 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472448 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472512 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 31533673 d431 d432
private def d426 : MobiusHarmonicTree := .branch 61047904 d427 d430
private def d418 : MobiusHarmonicTree := .branch 114877646 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472576 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472640 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 31212007 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472704 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472768 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 29748315 d439 d440
private def d434 : MobiusHarmonicTree := .branch 60960322 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472832 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472896 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 28384747 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 472960 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473024 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 30036576 d446 d447
private def d441 : MobiusHarmonicTree := .branch 58421323 d442 d445
private def d433 : MobiusHarmonicTree := .branch 119381645 d434 d441
private def d417 : MobiusHarmonicTree := .branch 234259291 d418 d433
private def d385 : MobiusHarmonicTree := .branch 440884365 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473088 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473152 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 27665716 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473216 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473280 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 27537712 d456 d457
private def d451 : MobiusHarmonicTree := .branch 55203428 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473344 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473408 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 22940143 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473472 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473536 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 22165285 d463 d464
private def d458 : MobiusHarmonicTree := .branch 45105428 d459 d462
private def d450 : MobiusHarmonicTree := .branch 100308856 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473600 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473664 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 21652569 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473728 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473792 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 23117783 d471 d472
private def d466 : MobiusHarmonicTree := .branch 44770352 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473856 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473920 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 21773872 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 473984 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474048 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 19274585 d478 d479
private def d473 : MobiusHarmonicTree := .branch 41048457 d474 d477
private def d465 : MobiusHarmonicTree := .branch 85818809 d466 d473
private def d449 : MobiusHarmonicTree := .branch 186127665 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474112 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474176 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 19960995 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474240 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474304 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 20132720 d487 d488
private def d482 : MobiusHarmonicTree := .branch 40093715 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474368 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474432 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 20964072 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474496 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474560 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 20313634 d494 d495
private def d489 : MobiusHarmonicTree := .branch 41277706 d490 d493
private def d481 : MobiusHarmonicTree := .branch 81371421 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474624 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474688 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 22343102 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474752 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474816 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 23485010 d502 d503
private def d497 : MobiusHarmonicTree := .branch 45828112 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474880 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 474944 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 19827757 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475008 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock057 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 475072 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 20234879 d509 d510
private def d504 : MobiusHarmonicTree := .branch 40062636 d505 d508
private def d496 : MobiusHarmonicTree := .branch 85890748 d497 d504
private def d480 : MobiusHarmonicTree := .branch 167262169 d481 d496
private def d448 : MobiusHarmonicTree := .branch 353389834 d449 d480
private def d384 : MobiusHarmonicTree := .branch 794274199 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1981419877 d257 d384
private def d0 : MobiusHarmonicTree := .branch 5353667806 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 458752 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 458752 5353667806 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 458752 3372247929 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 458752 1641280771 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 458752 720388524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 458752 307776011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 458752 144415331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 458752 70988560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 458752 36402465 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 458880 34586095 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 459008 73426771 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459008 35434573 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459136 37992198 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 459264 163360680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 459264 79442010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459264 39094214 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459392 40347796 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 459520 83918670 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459520 41924915 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459648 41993755 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 459776 412612513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 459776 191970206 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 459776 90575019 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459776 43736970 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 459904 46838049 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 460032 101395187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460032 50107061 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460160 51288126 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 460288 220642307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 460288 108267207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460288 53409202 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460416 54858005 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 460544 112375100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460544 55765639 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460672 56609461 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 460800 920892247 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 460800 445342209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 460800 225084637 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 460800 114233030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460800 57472581 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 460928 56760449 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 461056 110851607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461056 54662618 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461184 56188989 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 461312 220257572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 461312 108887772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461312 54903318 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461440 53984454 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 461568 111369800 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461568 55102465 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461696 56267335 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 461824 475550038 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 461824 239864075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 461824 117390903 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461824 57910234 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 461952 59480669 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 462080 122473172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462080 60704198 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462208 61768974 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 462336 235685963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 462336 118749286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462336 60145086 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462464 58604200 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 462592 116936677 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462592 57371036 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462720 59565641 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 462848 1730967158 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 462848 970330678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 462848 500595684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 462848 255880255 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 462848 124276399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462848 61193191 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 462976 63083208 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 463104 131603856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 463104 65684726 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 463232 65919130 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 463360 244715429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 463360 124675156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 463360 64284776 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 463488 60390380 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 463616 120040273 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 463616 59049476 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 463744 60990797 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 463872 469734994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 463872 240081632 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 463872 121724580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 463872 61318958 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464000 60405622 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 464128 118357052 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464128 58460798 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464256 59896254 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 464384 229653362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 464384 117304309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464384 59320052 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464512 57984257 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 464640 112349053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464640 56930994 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464768 55418059 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 464896 760636480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 464896 385650645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 464896 196292840 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 464896 103737448 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 464896 53421989 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465024 50315459 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 465152 92555392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465152 46900849 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465280 45654543 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 465408 189357805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 465408 91039353 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465408 45637652 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465536 45401701 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 465664 98318452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465664 48045312 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465792 50273140 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 465920 374985835 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 465920 190601885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 465920 97465139 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 465920 51079108 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466048 46386031 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 466176 93136746 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466176 46085798 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466304 47050948 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 466432 184383950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 466432 90552203 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466432 44836536 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466560 45715667 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 466688 93831747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466688 47457843 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466816 46373904 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 466944 1981419877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 466944 1187145678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 466944 665003647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 466944 359607543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 466944 187055644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 466944 94105681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 466944 47183469 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467072 46922212 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 467200 92949963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467200 46530542 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467328 46419421 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 467456 172551899 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 467456 90963608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467456 45726483 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467584 45237125 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 467712 81588291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467712 41549994 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467840 40038297 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 467968 305396104 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 467968 156606280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 467968 80372744 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 467968 40826296 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468096 39546448 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 468224 76233536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468224 38269334 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468352 37964202 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 468480 148789824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 468480 77542756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468480 39021000 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468608 38521756 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 468736 71247068 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468736 36245864 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468864 35001204 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 468992 522142031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 468992 262403060 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 468992 131561502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 468992 68095829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 468992 34168696 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 469120 33927133 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 469248 63465673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 469248 33025073 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 469376 30440600 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 469504 130841558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 469504 65374859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 469504 32900565 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 469632 32474294 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 469760 65466699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 469760 32448431 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 469888 33018268 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 470016 259738971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 470016 138630133 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 470016 71472268 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470016 36670468 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470144 34801800 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 470272 67157865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470272 33465482 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470400 33692383 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 470528 121108838 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 470528 63125002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470528 31938665 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470656 31186337 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 470784 57983836 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470784 30402690 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 470912 27581146 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 471040 794274199 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 471040 440884365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 471040 206625074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 471040 105163813 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 471040 56162824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471040 28063969 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471168 28098855 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 471296 49000989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471296 25492264 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471424 23508725 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 471552 101461261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 471552 48058021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471552 23894442 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471680 24163579 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 471808 53403240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471808 25797294 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 471936 27605946 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 472064 234259291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 472064 114877646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 472064 53829742 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472064 26139277 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472192 27690465 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 472320 61047904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472320 29514231 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472448 31533673 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 472576 119381645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 472576 60960322 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472576 31212007 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472704 29748315 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 472832 58421323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472832 28384747 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 472960 30036576 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 473088 353389834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 473088 186127665 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 473088 100308856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 473088 55203428 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473088 27665716 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473216 27537712 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 473344 45105428 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473344 22940143 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473472 22165285 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 473600 85818809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 473600 44770352 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473600 21652569 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473728 23117783 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 473856 41048457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473856 21773872 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 473984 19274585 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 474112 167262169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 474112 81371421 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 474112 40093715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 474112 19960995 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 474240 20132720 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 474368 41277706 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 474368 20964072 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 474496 20313634 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 474624 85890748 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 474624 45828112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 474624 22343102 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 474752 23485010 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 474880 40062636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 474880 19827757 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 475008 20234879 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 458752 (MobiusHarmonicTree.branch 5353667806 mobiusHarmonicBlock056 mobiusHarmonicBlock057) = true := Helfgott.combined

#print axioms solution
