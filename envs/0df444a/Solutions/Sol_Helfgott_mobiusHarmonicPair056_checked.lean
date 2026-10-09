-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair056_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:20:21.576707+00:00
-- url     : https://prove2.me/submissions/6570038d-b9bb-483b-8484-e1644ffe0b42

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917504 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917568 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 27073841 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917632 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917696 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 26509922 d11 d12
private def d6 : MobiusHarmonicTree := .branch 53583763 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917760 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917824 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 27128380 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917888 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 917952 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 25704047 d18 d19
private def d13 : MobiusHarmonicTree := .branch 52832427 d14 d17
private def d5 : MobiusHarmonicTree := .branch 106416190 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918016 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918080 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 25516386 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918144 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918208 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 26722768 d26 d27
private def d21 : MobiusHarmonicTree := .branch 52239154 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918272 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918336 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 27969129 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918400 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918464 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 28589134 d33 d34
private def d28 : MobiusHarmonicTree := .branch 56558263 d29 d32
private def d20 : MobiusHarmonicTree := .branch 108797417 d21 d28
private def d4 : MobiusHarmonicTree := .branch 215213607 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918528 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918592 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 27630417 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918656 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918720 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 28507136 d42 d43
private def d37 : MobiusHarmonicTree := .branch 56137553 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918784 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918848 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 29293246 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918912 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 918976 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 29413273 d49 d50
private def d44 : MobiusHarmonicTree := .branch 58706519 d45 d48
private def d36 : MobiusHarmonicTree := .branch 114844072 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919040 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919104 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 28934772 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919168 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919232 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 29666130 d57 d58
private def d52 : MobiusHarmonicTree := .branch 58600902 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919296 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919360 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 29855643 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919424 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919488 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 29930857 d64 d65
private def d59 : MobiusHarmonicTree := .branch 59786500 d60 d63
private def d51 : MobiusHarmonicTree := .branch 118387402 d52 d59
private def d35 : MobiusHarmonicTree := .branch 233231474 d36 d51
private def d3 : MobiusHarmonicTree := .branch 448445081 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919552 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919616 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 29622230 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919680 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919744 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 30151946 d74 d75
private def d69 : MobiusHarmonicTree := .branch 59774176 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919808 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919872 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 30414092 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 919936 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920000 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 31070729 d81 d82
private def d76 : MobiusHarmonicTree := .branch 61484821 d77 d80
private def d68 : MobiusHarmonicTree := .branch 121258997 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920064 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920128 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 30414324 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920192 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920256 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 30457904 d89 d90
private def d84 : MobiusHarmonicTree := .branch 60872228 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920320 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920384 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 30241798 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920448 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920512 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 31395634 d96 d97
private def d91 : MobiusHarmonicTree := .branch 61637432 d92 d95
private def d83 : MobiusHarmonicTree := .branch 122509660 d84 d91
private def d67 : MobiusHarmonicTree := .branch 243768657 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920576 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920640 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 30814523 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920704 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920768 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 31507459 d105 d106
private def d100 : MobiusHarmonicTree := .branch 62321982 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920832 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920896 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 31506365 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 920960 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921024 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 32377061 d112 d113
private def d107 : MobiusHarmonicTree := .branch 63883426 d108 d111
private def d99 : MobiusHarmonicTree := .branch 126205408 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921088 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921152 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 33099929 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921216 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921280 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 33093193 d120 d121
private def d115 : MobiusHarmonicTree := .branch 66193122 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921344 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921408 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 32444996 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921472 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921536 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 32542485 d127 d128
private def d122 : MobiusHarmonicTree := .branch 64987481 d123 d126
private def d114 : MobiusHarmonicTree := .branch 131180603 d115 d122
private def d98 : MobiusHarmonicTree := .branch 257386011 d99 d114
private def d66 : MobiusHarmonicTree := .branch 501154668 d67 d98
private def d2 : MobiusHarmonicTree := .branch 949599749 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921600 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921664 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 32667073 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921728 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921792 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 33400252 d138 d139
private def d133 : MobiusHarmonicTree := .branch 66067325 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921856 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921920 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 34295892 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 921984 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922048 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 34198921 d145 d146
private def d140 : MobiusHarmonicTree := .branch 68494813 d141 d144
private def d132 : MobiusHarmonicTree := .branch 134562138 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922112 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922176 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 35478127 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922240 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922304 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 36612723 d153 d154
private def d148 : MobiusHarmonicTree := .branch 72090850 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922368 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922432 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 36933984 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922496 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922560 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 37300655 d160 d161
private def d155 : MobiusHarmonicTree := .branch 74234639 d156 d159
private def d147 : MobiusHarmonicTree := .branch 146325489 d148 d155
private def d131 : MobiusHarmonicTree := .branch 280887627 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922624 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922688 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 35956997 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922752 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922816 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 35254128 d169 d170
private def d164 : MobiusHarmonicTree := .branch 71211125 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922880 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 922944 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 33639193 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923008 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923072 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 33568416 d176 d177
private def d171 : MobiusHarmonicTree := .branch 67207609 d172 d175
private def d163 : MobiusHarmonicTree := .branch 138418734 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923136 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923200 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 34383735 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923264 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923328 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 34344317 d184 d185
private def d179 : MobiusHarmonicTree := .branch 68728052 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923392 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923456 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 35318482 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923520 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923584 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 37472571 d191 d192
private def d186 : MobiusHarmonicTree := .branch 72791053 d187 d190
private def d178 : MobiusHarmonicTree := .branch 141519105 d179 d186
private def d162 : MobiusHarmonicTree := .branch 279937839 d163 d178
private def d130 : MobiusHarmonicTree := .branch 560825466 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923648 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923712 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 38101761 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923776 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923840 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 38915898 d201 d202
private def d196 : MobiusHarmonicTree := .branch 77017659 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923904 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 923968 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 40731973 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924032 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924096 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 42285732 d208 d209
private def d203 : MobiusHarmonicTree := .branch 83017705 d204 d207
private def d195 : MobiusHarmonicTree := .branch 160035364 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924160 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924224 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 41600419 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924288 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924352 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 40120070 d216 d217
private def d211 : MobiusHarmonicTree := .branch 81720489 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924416 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924480 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 41784633 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924544 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924608 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 42590014 d223 d224
private def d218 : MobiusHarmonicTree := .branch 84374647 d219 d222
private def d210 : MobiusHarmonicTree := .branch 166095136 d211 d218
private def d194 : MobiusHarmonicTree := .branch 326130500 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924672 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924736 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 44310026 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924800 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924864 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 44325520 d232 d233
private def d227 : MobiusHarmonicTree := .branch 88635546 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924928 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 924992 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 43930218 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925056 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925120 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 44620223 d239 d240
private def d234 : MobiusHarmonicTree := .branch 88550441 d235 d238
private def d226 : MobiusHarmonicTree := .branch 177185987 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925184 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925248 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 45967211 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925312 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925376 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 45648548 d247 d248
private def d242 : MobiusHarmonicTree := .branch 91615759 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925440 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925504 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 45406703 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925568 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock112 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925632 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 46003239 d254 d255
private def d249 : MobiusHarmonicTree := .branch 91409942 d250 d253
private def d241 : MobiusHarmonicTree := .branch 183025701 d242 d249
private def d225 : MobiusHarmonicTree := .branch 360211688 d226 d241
private def d193 : MobiusHarmonicTree := .branch 686342188 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1247167654 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2196767403 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925696 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925760 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 46386873 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925824 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925888 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 46087721 d266 d267
private def d261 : MobiusHarmonicTree := .branch 92474594 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 925952 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926016 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 47639651 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926080 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926144 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 48947099 d273 d274
private def d268 : MobiusHarmonicTree := .branch 96586750 d269 d272
private def d260 : MobiusHarmonicTree := .branch 189061344 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926208 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926272 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 49994034 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926336 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926400 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 49246646 d281 d282
private def d276 : MobiusHarmonicTree := .branch 99240680 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926464 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926528 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 47903673 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926592 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926656 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 47566817 d288 d289
private def d283 : MobiusHarmonicTree := .branch 95470490 d284 d287
private def d275 : MobiusHarmonicTree := .branch 194711170 d276 d283
private def d259 : MobiusHarmonicTree := .branch 383772514 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926720 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926784 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 47963822 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926848 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926912 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 47193341 d297 d298
private def d292 : MobiusHarmonicTree := .branch 95157163 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 926976 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927040 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 47371311 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927104 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927168 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 47333473 d304 d305
private def d299 : MobiusHarmonicTree := .branch 94704784 d300 d303
private def d291 : MobiusHarmonicTree := .branch 189861947 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927232 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927296 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 46508466 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927360 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927424 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 44549302 d312 d313
private def d307 : MobiusHarmonicTree := .branch 91057768 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927488 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927552 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 43937236 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927616 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927680 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 44258892 d319 d320
private def d314 : MobiusHarmonicTree := .branch 88196128 d315 d318
private def d306 : MobiusHarmonicTree := .branch 179253896 d307 d314
private def d290 : MobiusHarmonicTree := .branch 369115843 d291 d306
private def d258 : MobiusHarmonicTree := .branch 752888357 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927744 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927808 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 42428068 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927872 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 927936 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 41207681 d329 d330
private def d324 : MobiusHarmonicTree := .branch 83635749 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928000 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928064 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 41170727 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928128 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928192 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 41342831 d336 d337
private def d331 : MobiusHarmonicTree := .branch 82513558 d332 d335
private def d323 : MobiusHarmonicTree := .branch 166149307 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928256 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928320 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 39587730 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928384 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928448 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 38268254 d344 d345
private def d339 : MobiusHarmonicTree := .branch 77855984 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928512 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928576 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 36921154 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928640 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928704 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 36764228 d351 d352
private def d346 : MobiusHarmonicTree := .branch 73685382 d347 d350
private def d338 : MobiusHarmonicTree := .branch 151541366 d339 d346
private def d322 : MobiusHarmonicTree := .branch 317690673 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928768 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928832 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 35864487 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928896 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 928960 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 35600104 d360 d361
private def d355 : MobiusHarmonicTree := .branch 71464591 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929024 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929088 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 36168894 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929152 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929216 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 35160910 d367 d368
private def d362 : MobiusHarmonicTree := .branch 71329804 d363 d366
private def d354 : MobiusHarmonicTree := .branch 142794395 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929280 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929344 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 35029107 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929408 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929472 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 35228708 d375 d376
private def d370 : MobiusHarmonicTree := .branch 70257815 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929536 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929600 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 33946928 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929664 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929728 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 35302880 d382 d383
private def d377 : MobiusHarmonicTree := .branch 69249808 d378 d381
private def d369 : MobiusHarmonicTree := .branch 139507623 d370 d377
private def d353 : MobiusHarmonicTree := .branch 282302018 d354 d369
private def d321 : MobiusHarmonicTree := .branch 599992691 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1352881048 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929792 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929856 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 35955106 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929920 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 929984 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 36152324 d393 d394
private def d388 : MobiusHarmonicTree := .branch 72107430 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930048 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930112 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 35180822 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930176 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930240 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 34602979 d400 d401
private def d395 : MobiusHarmonicTree := .branch 69783801 d396 d399
private def d387 : MobiusHarmonicTree := .branch 141891231 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930304 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930368 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 33193437 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930432 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930496 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 33803534 d408 d409
private def d403 : MobiusHarmonicTree := .branch 66996971 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930560 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930624 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 33144522 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930688 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930752 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 32044079 d415 d416
private def d410 : MobiusHarmonicTree := .branch 65188601 d411 d414
private def d402 : MobiusHarmonicTree := .branch 132185572 d403 d410
private def d386 : MobiusHarmonicTree := .branch 274076803 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930816 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930880 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 31036300 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 930944 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931008 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 31106160 d424 d425
private def d419 : MobiusHarmonicTree := .branch 62142460 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931072 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931136 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 30383392 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931200 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931264 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 31100815 d431 d432
private def d426 : MobiusHarmonicTree := .branch 61484207 d427 d430
private def d418 : MobiusHarmonicTree := .branch 123626667 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931328 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931392 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 31120186 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931456 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931520 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 31090111 d439 d440
private def d434 : MobiusHarmonicTree := .branch 62210297 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931584 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931648 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 30884076 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931712 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931776 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 31031128 d446 d447
private def d441 : MobiusHarmonicTree := .branch 61915204 d442 d445
private def d433 : MobiusHarmonicTree := .branch 124125501 d434 d441
private def d417 : MobiusHarmonicTree := .branch 247752168 d418 d433
private def d385 : MobiusHarmonicTree := .branch 521828971 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931840 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931904 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 32559207 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 931968 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932032 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 34411985 d456 d457
private def d451 : MobiusHarmonicTree := .branch 66971192 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932096 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932160 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 33481479 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932224 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932288 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 32853666 d463 d464
private def d458 : MobiusHarmonicTree := .branch 66335145 d459 d462
private def d450 : MobiusHarmonicTree := .branch 133306337 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932352 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932416 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 33014305 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932480 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932544 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 34782325 d471 d472
private def d466 : MobiusHarmonicTree := .branch 67796630 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932608 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932672 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 36498441 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932736 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932800 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 36954408 d478 d479
private def d473 : MobiusHarmonicTree := .branch 73452849 d474 d477
private def d465 : MobiusHarmonicTree := .branch 141249479 d466 d473
private def d449 : MobiusHarmonicTree := .branch 274555816 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932864 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932928 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 37385618 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 932992 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933056 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 37759866 d487 d488
private def d482 : MobiusHarmonicTree := .branch 75145484 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933120 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933184 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 38564810 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933248 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933312 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 38757761 d494 d495
private def d489 : MobiusHarmonicTree := .branch 77322571 d490 d493
private def d481 : MobiusHarmonicTree := .branch 152468055 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933376 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933440 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 38305716 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933504 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933568 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 37394263 d502 d503
private def d497 : MobiusHarmonicTree := .branch 75699979 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933632 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933696 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 35461317 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933760 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock113 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933824 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 35622408 d509 d510
private def d504 : MobiusHarmonicTree := .branch 71083725 d505 d508
private def d496 : MobiusHarmonicTree := .branch 146783704 d497 d504
private def d480 : MobiusHarmonicTree := .branch 299251759 d481 d496
private def d448 : MobiusHarmonicTree := .branch 573807575 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1095636546 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2448517594 d257 d384
private def d0 : MobiusHarmonicTree := .branch 4645284997 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 917504 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 917504 4645284997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 917504 2196767403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 917504 949599749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 917504 448445081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 917504 215213607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 917504 106416190 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 917504 53583763 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 917504 27073841 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 917632 26509922 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 917760 52832427 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 917760 27128380 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 917888 25704047 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 918016 108797417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 918016 52239154 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918016 25516386 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918144 26722768 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 918272 56558263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918272 27969129 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918400 28589134 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 918528 233231474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 918528 114844072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 918528 56137553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918528 27630417 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918656 28507136 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 918784 58706519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918784 29293246 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 918912 29413273 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 919040 118387402 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 919040 58600902 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919040 28934772 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919168 29666130 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 919296 59786500 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919296 29855643 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919424 29930857 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 919552 501154668 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 919552 243768657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 919552 121258997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 919552 59774176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919552 29622230 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919680 30151946 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 919808 61484821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919808 30414092 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 919936 31070729 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 920064 122509660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 920064 60872228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920064 30414324 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920192 30457904 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 920320 61637432 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920320 30241798 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920448 31395634 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 920576 257386011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 920576 126205408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 920576 62321982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920576 30814523 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920704 31507459 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 920832 63883426 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920832 31506365 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 920960 32377061 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 921088 131180603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 921088 66193122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921088 33099929 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921216 33093193 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 921344 64987481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921344 32444996 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921472 32542485 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 921600 1247167654 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 921600 560825466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 921600 280887627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 921600 134562138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 921600 66067325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921600 32667073 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921728 33400252 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 921856 68494813 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921856 34295892 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 921984 34198921 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 922112 146325489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 922112 72090850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 922112 35478127 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 922240 36612723 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 922368 74234639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 922368 36933984 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 922496 37300655 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 922624 279937839 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 922624 138418734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 922624 71211125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 922624 35956997 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 922752 35254128 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 922880 67207609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 922880 33639193 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923008 33568416 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 923136 141519105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 923136 68728052 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923136 34383735 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923264 34344317 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 923392 72791053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923392 35318482 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923520 37472571 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 923648 686342188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 923648 326130500 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 923648 160035364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 923648 77017659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923648 38101761 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923776 38915898 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 923904 83017705 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 923904 40731973 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924032 42285732 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 924160 166095136 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 924160 81720489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924160 41600419 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924288 40120070 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 924416 84374647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924416 41784633 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924544 42590014 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 924672 360211688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 924672 177185987 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 924672 88635546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924672 44310026 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924800 44325520 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 924928 88550441 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 924928 43930218 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925056 44620223 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 925184 183025701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 925184 91615759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925184 45967211 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925312 45648548 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 925440 91409942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925440 45406703 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925568 46003239 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 925696 2448517594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 925696 1352881048 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 925696 752888357 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 925696 383772514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 925696 189061344 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 925696 92474594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925696 46386873 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925824 46087721 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 925952 96586750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 925952 47639651 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926080 48947099 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 926208 194711170 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 926208 99240680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926208 49994034 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926336 49246646 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 926464 95470490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926464 47903673 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926592 47566817 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 926720 369115843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 926720 189861947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 926720 95157163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926720 47963822 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926848 47193341 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 926976 94704784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 926976 47371311 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 927104 47333473 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 927232 179253896 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 927232 91057768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 927232 46508466 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 927360 44549302 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 927488 88196128 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 927488 43937236 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 927616 44258892 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 927744 599992691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 927744 317690673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 927744 166149307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 927744 83635749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 927744 42428068 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 927872 41207681 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 928000 82513558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928000 41170727 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928128 41342831 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 928256 151541366 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 928256 77855984 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928256 39587730 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928384 38268254 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 928512 73685382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928512 36921154 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928640 36764228 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 928768 282302018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 928768 142794395 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 928768 71464591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928768 35864487 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 928896 35600104 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 929024 71329804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929024 36168894 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929152 35160910 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 929280 139507623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 929280 70257815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929280 35029107 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929408 35228708 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 929536 69249808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929536 33946928 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929664 35302880 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 929792 1095636546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 929792 521828971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 929792 274076803 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 929792 141891231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 929792 72107430 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929792 35955106 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 929920 36152324 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 930048 69783801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930048 35180822 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930176 34602979 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 930304 132185572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 930304 66996971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930304 33193437 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930432 33803534 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 930560 65188601 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930560 33144522 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930688 32044079 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 930816 247752168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 930816 123626667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 930816 62142460 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930816 31036300 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 930944 31106160 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 931072 61484207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931072 30383392 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931200 31100815 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 931328 124125501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 931328 62210297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931328 31120186 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931456 31090111 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 931584 61915204 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931584 30884076 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931712 31031128 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 931840 573807575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 931840 274555816 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 931840 133306337 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 931840 66971192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931840 32559207 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 931968 34411985 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 932096 66335145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932096 33481479 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932224 32853666 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 932352 141249479 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 932352 67796630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932352 33014305 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932480 34782325 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 932608 73452849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932608 36498441 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932736 36954408 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 932864 299251759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 932864 152468055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 932864 75145484 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932864 37385618 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 932992 37759866 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 933120 77322571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 933120 38564810 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 933248 38757761 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 933376 146783704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 933376 75699979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 933376 38305716 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 933504 37394263 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 933632 71083725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 933632 35461317 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 933760 35622408 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 917504 (MobiusHarmonicTree.branch 4645284997 mobiusHarmonicBlock112 mobiusHarmonicBlock113) = true := Helfgott.combined

#print axioms solution
