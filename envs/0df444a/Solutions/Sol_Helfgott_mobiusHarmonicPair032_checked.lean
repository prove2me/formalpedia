-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair032_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:55:27.787879+00:00
-- url     : https://prove2.me/submissions/05e7dbfa-7312-4425-9a3f-2fb4a0063044

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524288 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524352 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 31063151 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524416 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524480 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 31881218 d11 d12
private def d6 : MobiusHarmonicTree := .branch 62944369 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524544 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524608 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 32954204 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524672 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524736 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 31111050 d18 d19
private def d13 : MobiusHarmonicTree := .branch 64065254 d14 d17
private def d5 : MobiusHarmonicTree := .branch 127009623 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524800 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524864 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 28666552 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524928 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524992 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 30937675 d26 d27
private def d21 : MobiusHarmonicTree := .branch 59604227 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525056 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525120 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 31766155 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525184 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525248 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 30966422 d33 d34
private def d28 : MobiusHarmonicTree := .branch 62732577 d29 d32
private def d20 : MobiusHarmonicTree := .branch 122336804 d21 d28
private def d4 : MobiusHarmonicTree := .branch 249346427 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525312 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525376 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 31390881 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525440 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525504 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 34755185 d42 d43
private def d37 : MobiusHarmonicTree := .branch 66146066 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525568 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525632 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 38696305 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525696 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525760 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 40423476 d49 d50
private def d44 : MobiusHarmonicTree := .branch 79119781 d45 d48
private def d36 : MobiusHarmonicTree := .branch 145265847 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525824 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525888 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 42588933 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 525952 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526016 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 46762936 d57 d58
private def d52 : MobiusHarmonicTree := .branch 89351869 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526080 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526144 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 47939495 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526208 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526272 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 44484787 d64 d65
private def d59 : MobiusHarmonicTree := .branch 92424282 d60 d63
private def d51 : MobiusHarmonicTree := .branch 181776151 d52 d59
private def d35 : MobiusHarmonicTree := .branch 327041998 d36 d51
private def d3 : MobiusHarmonicTree := .branch 576388425 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526336 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526400 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 42621661 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526464 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526528 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 44062359 d74 d75
private def d69 : MobiusHarmonicTree := .branch 86684020 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526592 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526656 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 44754125 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526720 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526784 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 47188312 d81 d82
private def d76 : MobiusHarmonicTree := .branch 91942437 d77 d80
private def d68 : MobiusHarmonicTree := .branch 178626457 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526848 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526912 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 47573535 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 526976 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527040 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 47214777 d89 d90
private def d84 : MobiusHarmonicTree := .branch 94788312 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527104 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527168 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 46683536 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527232 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527296 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 44826924 d96 d97
private def d91 : MobiusHarmonicTree := .branch 91510460 d92 d95
private def d83 : MobiusHarmonicTree := .branch 186298772 d84 d91
private def d67 : MobiusHarmonicTree := .branch 364925229 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527360 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527424 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 46967959 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527488 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527552 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 46452448 d105 d106
private def d100 : MobiusHarmonicTree := .branch 93420407 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527616 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527680 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 43814610 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527744 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527808 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 40643702 d112 d113
private def d107 : MobiusHarmonicTree := .branch 84458312 d108 d111
private def d99 : MobiusHarmonicTree := .branch 177878719 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527872 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 527936 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 40470912 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528000 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528064 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 41665496 d120 d121
private def d115 : MobiusHarmonicTree := .branch 82136408 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528128 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528192 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 42613361 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528256 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528320 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 40127333 d127 d128
private def d122 : MobiusHarmonicTree := .branch 82740694 d123 d126
private def d114 : MobiusHarmonicTree := .branch 164877102 d115 d122
private def d98 : MobiusHarmonicTree := .branch 342755821 d99 d114
private def d66 : MobiusHarmonicTree := .branch 707681050 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1284069475 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528384 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528448 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 39201696 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528512 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528576 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 37883092 d138 d139
private def d133 : MobiusHarmonicTree := .branch 77084788 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528640 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528704 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 35632536 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528768 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528832 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 36056868 d145 d146
private def d140 : MobiusHarmonicTree := .branch 71689404 d141 d144
private def d132 : MobiusHarmonicTree := .branch 148774192 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528896 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 528960 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 34479091 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529024 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529088 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 35464911 d153 d154
private def d148 : MobiusHarmonicTree := .branch 69944002 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529152 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529216 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 35494097 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529280 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529344 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 34854558 d160 d161
private def d155 : MobiusHarmonicTree := .branch 70348655 d156 d159
private def d147 : MobiusHarmonicTree := .branch 140292657 d148 d155
private def d131 : MobiusHarmonicTree := .branch 289066849 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529408 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529472 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 34545899 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529536 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529600 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 32294321 d169 d170
private def d164 : MobiusHarmonicTree := .branch 66840220 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529664 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529728 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 33137819 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529792 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529856 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 31540771 d176 d177
private def d171 : MobiusHarmonicTree := .branch 64678590 d172 d175
private def d163 : MobiusHarmonicTree := .branch 131518810 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529920 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 529984 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 29665125 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530048 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530112 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 29916414 d184 d185
private def d179 : MobiusHarmonicTree := .branch 59581539 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530176 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530240 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 31201075 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530304 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530368 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 30978604 d191 d192
private def d186 : MobiusHarmonicTree := .branch 62179679 d187 d190
private def d178 : MobiusHarmonicTree := .branch 121761218 d179 d186
private def d162 : MobiusHarmonicTree := .branch 253280028 d163 d178
private def d130 : MobiusHarmonicTree := .branch 542346877 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530432 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530496 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 30083290 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530560 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530624 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 28470398 d201 d202
private def d196 : MobiusHarmonicTree := .branch 58553688 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530688 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530752 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 26016043 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530816 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530880 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 23549674 d208 d209
private def d203 : MobiusHarmonicTree := .branch 49565717 d204 d207
private def d195 : MobiusHarmonicTree := .branch 108119405 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 530944 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531008 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 22960149 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531072 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531136 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 22668446 d216 d217
private def d211 : MobiusHarmonicTree := .branch 45628595 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531200 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531264 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 23517571 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531328 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531392 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 25612096 d223 d224
private def d218 : MobiusHarmonicTree := .branch 49129667 d219 d222
private def d210 : MobiusHarmonicTree := .branch 94758262 d211 d218
private def d194 : MobiusHarmonicTree := .branch 202877667 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531456 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531520 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 23306836 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531584 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531648 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 23985898 d232 d233
private def d227 : MobiusHarmonicTree := .branch 47292734 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531712 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531776 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 22283940 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531840 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531904 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 22991095 d239 d240
private def d234 : MobiusHarmonicTree := .branch 45275035 d235 d238
private def d226 : MobiusHarmonicTree := .branch 92567769 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 531968 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532032 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 24598228 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532096 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532160 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 22529055 d247 d248
private def d242 : MobiusHarmonicTree := .branch 47127283 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532224 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532288 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 20564163 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532352 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock064 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532416 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 21860760 d254 d255
private def d249 : MobiusHarmonicTree := .branch 42424923 d250 d253
private def d241 : MobiusHarmonicTree := .branch 89552206 d242 d249
private def d225 : MobiusHarmonicTree := .branch 182119975 d226 d241
private def d193 : MobiusHarmonicTree := .branch 384997642 d194 d225
private def d129 : MobiusHarmonicTree := .branch 927344519 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2211413994 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532480 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532544 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 23348365 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532608 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532672 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 25345881 d266 d267
private def d261 : MobiusHarmonicTree := .branch 48694246 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532736 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532800 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 25317255 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532864 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532928 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 26525248 d273 d274
private def d268 : MobiusHarmonicTree := .branch 51842503 d269 d272
private def d260 : MobiusHarmonicTree := .branch 100536749 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 532992 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533056 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 26327517 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533120 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533184 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 28341086 d281 d282
private def d276 : MobiusHarmonicTree := .branch 54668603 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533248 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533312 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 29208163 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533376 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533440 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 27800803 d288 d289
private def d283 : MobiusHarmonicTree := .branch 57008966 d284 d287
private def d275 : MobiusHarmonicTree := .branch 111677569 d276 d283
private def d259 : MobiusHarmonicTree := .branch 212214318 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533504 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533568 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 25732522 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533632 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533696 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 22469920 d297 d298
private def d292 : MobiusHarmonicTree := .branch 48202442 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533760 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533824 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 20195896 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533888 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 533952 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 19623586 d304 d305
private def d299 : MobiusHarmonicTree := .branch 39819482 d300 d303
private def d291 : MobiusHarmonicTree := .branch 88021924 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534016 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534080 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 21991078 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534144 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534208 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 25956231 d312 d313
private def d307 : MobiusHarmonicTree := .branch 47947309 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534272 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534336 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 27789651 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534400 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534464 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 28035676 d319 d320
private def d314 : MobiusHarmonicTree := .branch 55825327 d315 d318
private def d306 : MobiusHarmonicTree := .branch 103772636 d307 d314
private def d290 : MobiusHarmonicTree := .branch 191794560 d291 d306
private def d258 : MobiusHarmonicTree := .branch 404008878 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534528 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534592 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 26021846 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534656 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534720 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 27713637 d329 d330
private def d324 : MobiusHarmonicTree := .branch 53735483 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534784 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534848 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 25900951 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534912 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 534976 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 23991858 d336 d337
private def d331 : MobiusHarmonicTree := .branch 49892809 d332 d335
private def d323 : MobiusHarmonicTree := .branch 103628292 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535040 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535104 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 22091148 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535168 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535232 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 20981689 d344 d345
private def d339 : MobiusHarmonicTree := .branch 43072837 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535296 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535360 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 17937585 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535424 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535488 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 14670877 d351 d352
private def d346 : MobiusHarmonicTree := .branch 32608462 d347 d350
private def d338 : MobiusHarmonicTree := .branch 75681299 d339 d346
private def d322 : MobiusHarmonicTree := .branch 179309591 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535552 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535616 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 13478063 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535680 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535744 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 13071604 d360 d361
private def d355 : MobiusHarmonicTree := .branch 26549667 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535808 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535872 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 11170657 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 535936 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536000 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 12794827 d367 d368
private def d362 : MobiusHarmonicTree := .branch 23965484 d363 d366
private def d354 : MobiusHarmonicTree := .branch 50515151 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536064 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536128 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 11124341 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536192 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536256 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 13778855 d375 d376
private def d370 : MobiusHarmonicTree := .branch 24903196 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536320 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536384 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 14918503 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536448 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536512 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 16227124 d382 d383
private def d377 : MobiusHarmonicTree := .branch 31145627 d378 d381
private def d369 : MobiusHarmonicTree := .branch 56048823 d370 d377
private def d353 : MobiusHarmonicTree := .branch 106563974 d354 d369
private def d321 : MobiusHarmonicTree := .branch 285873565 d322 d353
private def d257 : MobiusHarmonicTree := .branch 689882443 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536576 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536640 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 16053636 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536704 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536768 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 16793141 d393 d394
private def d388 : MobiusHarmonicTree := .branch 32846777 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536832 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536896 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 18541852 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 536960 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537024 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 20792388 d400 d401
private def d395 : MobiusHarmonicTree := .branch 39334240 d396 d399
private def d387 : MobiusHarmonicTree := .branch 72181017 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537088 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537152 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 23114503 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537216 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537280 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 23732646 d408 d409
private def d403 : MobiusHarmonicTree := .branch 46847149 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537344 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537408 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 22087601 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537472 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537536 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 19887148 d415 d416
private def d410 : MobiusHarmonicTree := .branch 41974749 d411 d414
private def d402 : MobiusHarmonicTree := .branch 88821898 d403 d410
private def d386 : MobiusHarmonicTree := .branch 161002915 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537600 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537664 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 18952464 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537728 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537792 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 19369976 d424 d425
private def d419 : MobiusHarmonicTree := .branch 38322440 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537856 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537920 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 18575329 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 537984 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538048 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 18057912 d431 d432
private def d426 : MobiusHarmonicTree := .branch 36633241 d427 d430
private def d418 : MobiusHarmonicTree := .branch 74955681 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538112 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538176 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 17797292 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538240 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538304 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 17415832 d439 d440
private def d434 : MobiusHarmonicTree := .branch 35213124 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538368 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538432 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 16453434 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538496 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538560 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 19271731 d446 d447
private def d441 : MobiusHarmonicTree := .branch 35725165 d442 d445
private def d433 : MobiusHarmonicTree := .branch 70938289 d434 d441
private def d417 : MobiusHarmonicTree := .branch 145893970 d418 d433
private def d385 : MobiusHarmonicTree := .branch 306896885 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538624 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538688 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 17670837 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538752 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538816 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 16239388 d456 d457
private def d451 : MobiusHarmonicTree := .branch 33910225 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538880 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 538944 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 15190905 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539008 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539072 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 14881237 d463 d464
private def d458 : MobiusHarmonicTree := .branch 30072142 d459 d462
private def d450 : MobiusHarmonicTree := .branch 63982367 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539136 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539200 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 13362522 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539264 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539328 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 12523083 d471 d472
private def d466 : MobiusHarmonicTree := .branch 25885605 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539392 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539456 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 12479374 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539520 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539584 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 9457369 d478 d479
private def d473 : MobiusHarmonicTree := .branch 21936743 d474 d477
private def d465 : MobiusHarmonicTree := .branch 47822348 d466 d473
private def d449 : MobiusHarmonicTree := .branch 111804715 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539648 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539712 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 9657097 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539776 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539840 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 10716193 d487 d488
private def d482 : MobiusHarmonicTree := .branch 20373290 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539904 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 539968 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 12035942 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540032 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540096 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 11890601 d494 d495
private def d489 : MobiusHarmonicTree := .branch 23926543 d490 d493
private def d481 : MobiusHarmonicTree := .branch 44299833 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540160 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540224 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 11724812 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540288 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540352 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 11098386 d502 d503
private def d497 : MobiusHarmonicTree := .branch 22823198 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540416 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540480 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 11408453 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540544 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock065 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540608 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 13277669 d509 d510
private def d504 : MobiusHarmonicTree := .branch 24686122 d505 d508
private def d496 : MobiusHarmonicTree := .branch 47509320 d497 d504
private def d480 : MobiusHarmonicTree := .branch 91809153 d481 d496
private def d448 : MobiusHarmonicTree := .branch 203613868 d449 d480
private def d384 : MobiusHarmonicTree := .branch 510510753 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1200393196 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3411807190 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 524288 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 524288 3411807190 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 524288 2211413994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 524288 1284069475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 524288 576388425 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 524288 249346427 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 524288 127009623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 524288 62944369 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524288 31063151 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524416 31881218 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 524544 64065254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524544 32954204 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524672 31111050 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 524800 122336804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 524800 59604227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524800 28666552 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524928 30937675 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 525056 62732577 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525056 31766155 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525184 30966422 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 525312 327041998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 525312 145265847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 525312 66146066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525312 31390881 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525440 34755185 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 525568 79119781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525568 38696305 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525696 40423476 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 525824 181776151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 525824 89351869 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525824 42588933 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 525952 46762936 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 526080 92424282 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526080 47939495 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526208 44484787 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 526336 707681050 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 526336 364925229 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 526336 178626457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 526336 86684020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526336 42621661 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526464 44062359 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 526592 91942437 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526592 44754125 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526720 47188312 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 526848 186298772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 526848 94788312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526848 47573535 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 526976 47214777 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 527104 91510460 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 527104 46683536 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 527232 44826924 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 527360 342755821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 527360 177878719 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 527360 93420407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 527360 46967959 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 527488 46452448 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 527616 84458312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 527616 43814610 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 527744 40643702 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 527872 164877102 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 527872 82136408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 527872 40470912 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528000 41665496 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 528128 82740694 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528128 42613361 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528256 40127333 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 528384 927344519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 528384 542346877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 528384 289066849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 528384 148774192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 528384 77084788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528384 39201696 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528512 37883092 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 528640 71689404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528640 35632536 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528768 36056868 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 528896 140292657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 528896 69944002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 528896 34479091 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529024 35464911 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 529152 70348655 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529152 35494097 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529280 34854558 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 529408 253280028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 529408 131518810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 529408 66840220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529408 34545899 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529536 32294321 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 529664 64678590 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529664 33137819 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529792 31540771 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 529920 121761218 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 529920 59581539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 529920 29665125 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530048 29916414 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 530176 62179679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530176 31201075 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530304 30978604 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 530432 384997642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 530432 202877667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 530432 108119405 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 530432 58553688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530432 30083290 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530560 28470398 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 530688 49565717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530688 26016043 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530816 23549674 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 530944 94758262 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 530944 45628595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 530944 22960149 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531072 22668446 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 531200 49129667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531200 23517571 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531328 25612096 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 531456 182119975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 531456 92567769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 531456 47292734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531456 23306836 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531584 23985898 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 531712 45275035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531712 22283940 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531840 22991095 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 531968 89552206 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 531968 47127283 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 531968 24598228 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532096 22529055 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 532224 42424923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532224 20564163 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532352 21860760 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 532480 1200393196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 532480 689882443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 532480 404008878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 532480 212214318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 532480 100536749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 532480 48694246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532480 23348365 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532608 25345881 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 532736 51842503 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532736 25317255 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532864 26525248 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 532992 111677569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 532992 54668603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 532992 26327517 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 533120 28341086 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 533248 57008966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 533248 29208163 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 533376 27800803 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 533504 191794560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 533504 88021924 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 533504 48202442 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 533504 25732522 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 533632 22469920 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 533760 39819482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 533760 20195896 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 533888 19623586 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 534016 103772636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 534016 47947309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534016 21991078 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534144 25956231 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 534272 55825327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534272 27789651 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534400 28035676 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 534528 285873565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 534528 179309591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 534528 103628292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 534528 53735483 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534528 26021846 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534656 27713637 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 534784 49892809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534784 25900951 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 534912 23991858 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 535040 75681299 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 535040 43072837 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535040 22091148 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535168 20981689 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 535296 32608462 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535296 17937585 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535424 14670877 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 535552 106563974 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 535552 50515151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 535552 26549667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535552 13478063 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535680 13071604 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 535808 23965484 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535808 11170657 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 535936 12794827 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 536064 56048823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 536064 24903196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536064 11124341 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536192 13778855 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 536320 31145627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536320 14918503 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536448 16227124 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 536576 510510753 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 536576 306896885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 536576 161002915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 536576 72181017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 536576 32846777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536576 16053636 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536704 16793141 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 536832 39334240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536832 18541852 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 536960 20792388 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 537088 88821898 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 537088 46847149 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537088 23114503 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537216 23732646 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 537344 41974749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537344 22087601 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537472 19887148 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 537600 145893970 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 537600 74955681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 537600 38322440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537600 18952464 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537728 19369976 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 537856 36633241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537856 18575329 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 537984 18057912 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 538112 70938289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 538112 35213124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 538112 17797292 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 538240 17415832 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 538368 35725165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 538368 16453434 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 538496 19271731 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 538624 203613868 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 538624 111804715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 538624 63982367 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 538624 33910225 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 538624 17670837 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 538752 16239388 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 538880 30072142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 538880 15190905 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539008 14881237 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 539136 47822348 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 539136 25885605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539136 13362522 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539264 12523083 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 539392 21936743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539392 12479374 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539520 9457369 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 539648 91809153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 539648 44299833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 539648 20373290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539648 9657097 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539776 10716193 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 539904 23926543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 539904 12035942 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540032 11890601 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 540160 47509320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 540160 22823198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540160 11724812 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540288 11098386 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 540416 24686122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540416 11408453 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540544 13277669 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 524288 (MobiusHarmonicTree.branch 3411807190 mobiusHarmonicBlock064 mobiusHarmonicBlock065) = true := Helfgott.combined

#print axioms solution
