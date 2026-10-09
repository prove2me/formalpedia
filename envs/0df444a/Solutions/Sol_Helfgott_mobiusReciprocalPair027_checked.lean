-- Prove2me | solution 1 for Helfgott.mobiusReciprocalPair027_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:56:17.450994+00:00
-- url     : https://prove2.me/submissions/2411b881-63e9-4a2a-b6d7-241bf35e104f

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
import Definitions.Def_Helfgott_MobiusReciprocalCertificate
import Mathlib.Tactic

section
set_option autoImplicit false
namespace Helfgott

theorem mobiusReciprocalTreeCheck_join (g : ℕ → ℤ) (Q A B d offset : ℕ)
    (l r : MobiusReciprocalTree) (hoff : offset < B)
    (hl : mobiusReciprocalTreeCheck g Q A B d offset l = true)
    (hr : mobiusReciprocalTreeCheck g Q A B d (offset + 32 * 2 ^ d) r = true)
    (hjoin : mobiusReciprocalFinish l = mobiusReciprocalStart r) :
    mobiusReciprocalTreeCheck g Q A B (d + 1) offset (.branch l r) = true := by
  have hnot : ¬ B ≤ offset := by omega
  simp only [mobiusReciprocalTreeCheck, if_neg hnot, hl, hr, hjoin,
    beq_self_eq_true, Bool.and_self]

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Helfgott

private def publishedReciprocalLeaf : ℕ → MobiusReciprocalTree → ℕ → MobiusReciprocalTree
  | 0, tree, _ => tree
  | d + 1, .branch l r, k =>
      if k < 2 ^ d then publishedReciprocalLeaf d l k else publishedReciprocalLeaf d r (k - 2 ^ d)
  | _, tree, _ => tree

private abbrev r8 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 0
private theorem rc8 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442368 r8 = true := by decide +kernel

private abbrev r9 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 1
private theorem rc9 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442432 r9 = true := by decide +kernel

private def r7 : MobiusReciprocalTree := .branch r8 r9
private abbrev r11 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 2
private theorem rc11 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442496 r11 = true := by decide +kernel

private abbrev r12 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 3
private theorem rc12 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442560 r12 = true := by decide +kernel

private def r10 : MobiusReciprocalTree := .branch r11 r12
private def r6 : MobiusReciprocalTree := .branch r7 r10
private abbrev r15 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 4
private theorem rc15 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442624 r15 = true := by decide +kernel

private abbrev r16 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 5
private theorem rc16 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442688 r16 = true := by decide +kernel

private def r14 : MobiusReciprocalTree := .branch r15 r16
private abbrev r18 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 6
private theorem rc18 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442752 r18 = true := by decide +kernel

private abbrev r19 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 7
private theorem rc19 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442816 r19 = true := by decide +kernel

private def r17 : MobiusReciprocalTree := .branch r18 r19
private def r13 : MobiusReciprocalTree := .branch r14 r17
private def r5 : MobiusReciprocalTree := .branch r6 r13
private abbrev r23 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 8
private theorem rc23 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442880 r23 = true := by decide +kernel

private abbrev r24 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 9
private theorem rc24 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442944 r24 = true := by decide +kernel

private def r22 : MobiusReciprocalTree := .branch r23 r24
private abbrev r26 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 10
private theorem rc26 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443008 r26 = true := by decide +kernel

private abbrev r27 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 11
private theorem rc27 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443072 r27 = true := by decide +kernel

private def r25 : MobiusReciprocalTree := .branch r26 r27
private def r21 : MobiusReciprocalTree := .branch r22 r25
private abbrev r30 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 12
private theorem rc30 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443136 r30 = true := by decide +kernel

private abbrev r31 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 13
private theorem rc31 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443200 r31 = true := by decide +kernel

private def r29 : MobiusReciprocalTree := .branch r30 r31
private abbrev r33 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 14
private theorem rc33 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443264 r33 = true := by decide +kernel

private abbrev r34 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 15
private theorem rc34 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443328 r34 = true := by decide +kernel

private def r32 : MobiusReciprocalTree := .branch r33 r34
private def r28 : MobiusReciprocalTree := .branch r29 r32
private def r20 : MobiusReciprocalTree := .branch r21 r28
private def r4 : MobiusReciprocalTree := .branch r5 r20
private abbrev r39 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 16
private theorem rc39 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443392 r39 = true := by decide +kernel

private abbrev r40 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 17
private theorem rc40 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443456 r40 = true := by decide +kernel

private def r38 : MobiusReciprocalTree := .branch r39 r40
private abbrev r42 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 18
private theorem rc42 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443520 r42 = true := by decide +kernel

private abbrev r43 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 19
private theorem rc43 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443584 r43 = true := by decide +kernel

private def r41 : MobiusReciprocalTree := .branch r42 r43
private def r37 : MobiusReciprocalTree := .branch r38 r41
private abbrev r46 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 20
private theorem rc46 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443648 r46 = true := by decide +kernel

private abbrev r47 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 21
private theorem rc47 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443712 r47 = true := by decide +kernel

private def r45 : MobiusReciprocalTree := .branch r46 r47
private abbrev r49 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 22
private theorem rc49 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443776 r49 = true := by decide +kernel

private abbrev r50 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 23
private theorem rc50 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443840 r50 = true := by decide +kernel

private def r48 : MobiusReciprocalTree := .branch r49 r50
private def r44 : MobiusReciprocalTree := .branch r45 r48
private def r36 : MobiusReciprocalTree := .branch r37 r44
private abbrev r54 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 24
private theorem rc54 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443904 r54 = true := by decide +kernel

private abbrev r55 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 25
private theorem rc55 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443968 r55 = true := by decide +kernel

private def r53 : MobiusReciprocalTree := .branch r54 r55
private abbrev r57 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 26
private theorem rc57 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444032 r57 = true := by decide +kernel

private abbrev r58 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 27
private theorem rc58 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444096 r58 = true := by decide +kernel

private def r56 : MobiusReciprocalTree := .branch r57 r58
private def r52 : MobiusReciprocalTree := .branch r53 r56
private abbrev r61 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 28
private theorem rc61 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444160 r61 = true := by decide +kernel

private abbrev r62 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 29
private theorem rc62 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444224 r62 = true := by decide +kernel

private def r60 : MobiusReciprocalTree := .branch r61 r62
private abbrev r64 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 30
private theorem rc64 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444288 r64 = true := by decide +kernel

private abbrev r65 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 31
private theorem rc65 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444352 r65 = true := by decide +kernel

private def r63 : MobiusReciprocalTree := .branch r64 r65
private def r59 : MobiusReciprocalTree := .branch r60 r63
private def r51 : MobiusReciprocalTree := .branch r52 r59
private def r35 : MobiusReciprocalTree := .branch r36 r51
private def r3 : MobiusReciprocalTree := .branch r4 r35
private abbrev r71 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 32
private theorem rc71 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444416 r71 = true := by decide +kernel

private abbrev r72 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 33
private theorem rc72 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444480 r72 = true := by decide +kernel

private def r70 : MobiusReciprocalTree := .branch r71 r72
private abbrev r74 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 34
private theorem rc74 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444544 r74 = true := by decide +kernel

private abbrev r75 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 35
private theorem rc75 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444608 r75 = true := by decide +kernel

private def r73 : MobiusReciprocalTree := .branch r74 r75
private def r69 : MobiusReciprocalTree := .branch r70 r73
private abbrev r78 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 36
private theorem rc78 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444672 r78 = true := by decide +kernel

private abbrev r79 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 37
private theorem rc79 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444736 r79 = true := by decide +kernel

private def r77 : MobiusReciprocalTree := .branch r78 r79
private abbrev r81 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 38
private theorem rc81 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444800 r81 = true := by decide +kernel

private abbrev r82 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 39
private theorem rc82 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444864 r82 = true := by decide +kernel

private def r80 : MobiusReciprocalTree := .branch r81 r82
private def r76 : MobiusReciprocalTree := .branch r77 r80
private def r68 : MobiusReciprocalTree := .branch r69 r76
private abbrev r86 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 40
private theorem rc86 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444928 r86 = true := by decide +kernel

private abbrev r87 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 41
private theorem rc87 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444992 r87 = true := by decide +kernel

private def r85 : MobiusReciprocalTree := .branch r86 r87
private abbrev r89 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 42
private theorem rc89 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445056 r89 = true := by decide +kernel

private abbrev r90 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 43
private theorem rc90 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445120 r90 = true := by decide +kernel

private def r88 : MobiusReciprocalTree := .branch r89 r90
private def r84 : MobiusReciprocalTree := .branch r85 r88
private abbrev r93 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 44
private theorem rc93 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445184 r93 = true := by decide +kernel

private abbrev r94 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 45
private theorem rc94 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445248 r94 = true := by decide +kernel

private def r92 : MobiusReciprocalTree := .branch r93 r94
private abbrev r96 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 46
private theorem rc96 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445312 r96 = true := by decide +kernel

private abbrev r97 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 47
private theorem rc97 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445376 r97 = true := by decide +kernel

private def r95 : MobiusReciprocalTree := .branch r96 r97
private def r91 : MobiusReciprocalTree := .branch r92 r95
private def r83 : MobiusReciprocalTree := .branch r84 r91
private def r67 : MobiusReciprocalTree := .branch r68 r83
private abbrev r102 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 48
private theorem rc102 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445440 r102 = true := by decide +kernel

private abbrev r103 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 49
private theorem rc103 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445504 r103 = true := by decide +kernel

private def r101 : MobiusReciprocalTree := .branch r102 r103
private abbrev r105 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 50
private theorem rc105 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445568 r105 = true := by decide +kernel

private abbrev r106 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 51
private theorem rc106 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445632 r106 = true := by decide +kernel

private def r104 : MobiusReciprocalTree := .branch r105 r106
private def r100 : MobiusReciprocalTree := .branch r101 r104
private abbrev r109 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 52
private theorem rc109 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445696 r109 = true := by decide +kernel

private abbrev r110 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 53
private theorem rc110 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445760 r110 = true := by decide +kernel

private def r108 : MobiusReciprocalTree := .branch r109 r110
private abbrev r112 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 54
private theorem rc112 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445824 r112 = true := by decide +kernel

private abbrev r113 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 55
private theorem rc113 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445888 r113 = true := by decide +kernel

private def r111 : MobiusReciprocalTree := .branch r112 r113
private def r107 : MobiusReciprocalTree := .branch r108 r111
private def r99 : MobiusReciprocalTree := .branch r100 r107
private abbrev r117 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 56
private theorem rc117 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445952 r117 = true := by decide +kernel

private abbrev r118 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 57
private theorem rc118 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446016 r118 = true := by decide +kernel

private def r116 : MobiusReciprocalTree := .branch r117 r118
private abbrev r120 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 58
private theorem rc120 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446080 r120 = true := by decide +kernel

private abbrev r121 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 59
private theorem rc121 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446144 r121 = true := by decide +kernel

private def r119 : MobiusReciprocalTree := .branch r120 r121
private def r115 : MobiusReciprocalTree := .branch r116 r119
private abbrev r124 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 60
private theorem rc124 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446208 r124 = true := by decide +kernel

private abbrev r125 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 61
private theorem rc125 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446272 r125 = true := by decide +kernel

private def r123 : MobiusReciprocalTree := .branch r124 r125
private abbrev r127 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 62
private theorem rc127 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446336 r127 = true := by decide +kernel

private abbrev r128 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 63
private theorem rc128 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446400 r128 = true := by decide +kernel

private def r126 : MobiusReciprocalTree := .branch r127 r128
private def r122 : MobiusReciprocalTree := .branch r123 r126
private def r114 : MobiusReciprocalTree := .branch r115 r122
private def r98 : MobiusReciprocalTree := .branch r99 r114
private def r66 : MobiusReciprocalTree := .branch r67 r98
private def r2 : MobiusReciprocalTree := .branch r3 r66
private abbrev r135 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 64
private theorem rc135 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446464 r135 = true := by decide +kernel

private abbrev r136 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 65
private theorem rc136 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446528 r136 = true := by decide +kernel

private def r134 : MobiusReciprocalTree := .branch r135 r136
private abbrev r138 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 66
private theorem rc138 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446592 r138 = true := by decide +kernel

private abbrev r139 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 67
private theorem rc139 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446656 r139 = true := by decide +kernel

private def r137 : MobiusReciprocalTree := .branch r138 r139
private def r133 : MobiusReciprocalTree := .branch r134 r137
private abbrev r142 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 68
private theorem rc142 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446720 r142 = true := by decide +kernel

private abbrev r143 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 69
private theorem rc143 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446784 r143 = true := by decide +kernel

private def r141 : MobiusReciprocalTree := .branch r142 r143
private abbrev r145 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 70
private theorem rc145 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446848 r145 = true := by decide +kernel

private abbrev r146 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 71
private theorem rc146 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446912 r146 = true := by decide +kernel

private def r144 : MobiusReciprocalTree := .branch r145 r146
private def r140 : MobiusReciprocalTree := .branch r141 r144
private def r132 : MobiusReciprocalTree := .branch r133 r140
private abbrev r150 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 72
private theorem rc150 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446976 r150 = true := by decide +kernel

private abbrev r151 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 73
private theorem rc151 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447040 r151 = true := by decide +kernel

private def r149 : MobiusReciprocalTree := .branch r150 r151
private abbrev r153 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 74
private theorem rc153 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447104 r153 = true := by decide +kernel

private abbrev r154 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 75
private theorem rc154 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447168 r154 = true := by decide +kernel

private def r152 : MobiusReciprocalTree := .branch r153 r154
private def r148 : MobiusReciprocalTree := .branch r149 r152
private abbrev r157 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 76
private theorem rc157 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447232 r157 = true := by decide +kernel

private abbrev r158 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 77
private theorem rc158 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447296 r158 = true := by decide +kernel

private def r156 : MobiusReciprocalTree := .branch r157 r158
private abbrev r160 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 78
private theorem rc160 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447360 r160 = true := by decide +kernel

private abbrev r161 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 79
private theorem rc161 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447424 r161 = true := by decide +kernel

private def r159 : MobiusReciprocalTree := .branch r160 r161
private def r155 : MobiusReciprocalTree := .branch r156 r159
private def r147 : MobiusReciprocalTree := .branch r148 r155
private def r131 : MobiusReciprocalTree := .branch r132 r147
private abbrev r166 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 80
private theorem rc166 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447488 r166 = true := by decide +kernel

private abbrev r167 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 81
private theorem rc167 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447552 r167 = true := by decide +kernel

private def r165 : MobiusReciprocalTree := .branch r166 r167
private abbrev r169 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 82
private theorem rc169 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447616 r169 = true := by decide +kernel

private abbrev r170 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 83
private theorem rc170 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447680 r170 = true := by decide +kernel

private def r168 : MobiusReciprocalTree := .branch r169 r170
private def r164 : MobiusReciprocalTree := .branch r165 r168
private abbrev r173 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 84
private theorem rc173 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447744 r173 = true := by decide +kernel

private abbrev r174 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 85
private theorem rc174 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447808 r174 = true := by decide +kernel

private def r172 : MobiusReciprocalTree := .branch r173 r174
private abbrev r176 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 86
private theorem rc176 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447872 r176 = true := by decide +kernel

private abbrev r177 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 87
private theorem rc177 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447936 r177 = true := by decide +kernel

private def r175 : MobiusReciprocalTree := .branch r176 r177
private def r171 : MobiusReciprocalTree := .branch r172 r175
private def r163 : MobiusReciprocalTree := .branch r164 r171
private abbrev r181 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 88
private theorem rc181 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448000 r181 = true := by decide +kernel

private abbrev r182 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 89
private theorem rc182 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448064 r182 = true := by decide +kernel

private def r180 : MobiusReciprocalTree := .branch r181 r182
private abbrev r184 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 90
private theorem rc184 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448128 r184 = true := by decide +kernel

private abbrev r185 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 91
private theorem rc185 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448192 r185 = true := by decide +kernel

private def r183 : MobiusReciprocalTree := .branch r184 r185
private def r179 : MobiusReciprocalTree := .branch r180 r183
private abbrev r188 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 92
private theorem rc188 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448256 r188 = true := by decide +kernel

private abbrev r189 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 93
private theorem rc189 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448320 r189 = true := by decide +kernel

private def r187 : MobiusReciprocalTree := .branch r188 r189
private abbrev r191 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 94
private theorem rc191 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448384 r191 = true := by decide +kernel

private abbrev r192 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 95
private theorem rc192 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448448 r192 = true := by decide +kernel

private def r190 : MobiusReciprocalTree := .branch r191 r192
private def r186 : MobiusReciprocalTree := .branch r187 r190
private def r178 : MobiusReciprocalTree := .branch r179 r186
private def r162 : MobiusReciprocalTree := .branch r163 r178
private def r130 : MobiusReciprocalTree := .branch r131 r162
private abbrev r198 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 96
private theorem rc198 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448512 r198 = true := by decide +kernel

private abbrev r199 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 97
private theorem rc199 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448576 r199 = true := by decide +kernel

private def r197 : MobiusReciprocalTree := .branch r198 r199
private abbrev r201 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 98
private theorem rc201 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448640 r201 = true := by decide +kernel

private abbrev r202 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 99
private theorem rc202 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448704 r202 = true := by decide +kernel

private def r200 : MobiusReciprocalTree := .branch r201 r202
private def r196 : MobiusReciprocalTree := .branch r197 r200
private abbrev r205 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 100
private theorem rc205 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448768 r205 = true := by decide +kernel

private abbrev r206 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 101
private theorem rc206 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448832 r206 = true := by decide +kernel

private def r204 : MobiusReciprocalTree := .branch r205 r206
private abbrev r208 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 102
private theorem rc208 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448896 r208 = true := by decide +kernel

private abbrev r209 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 103
private theorem rc209 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448960 r209 = true := by decide +kernel

private def r207 : MobiusReciprocalTree := .branch r208 r209
private def r203 : MobiusReciprocalTree := .branch r204 r207
private def r195 : MobiusReciprocalTree := .branch r196 r203
private abbrev r213 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 104
private theorem rc213 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449024 r213 = true := by decide +kernel

private abbrev r214 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 105
private theorem rc214 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449088 r214 = true := by decide +kernel

private def r212 : MobiusReciprocalTree := .branch r213 r214
private abbrev r216 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 106
private theorem rc216 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449152 r216 = true := by decide +kernel

private abbrev r217 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 107
private theorem rc217 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449216 r217 = true := by decide +kernel

private def r215 : MobiusReciprocalTree := .branch r216 r217
private def r211 : MobiusReciprocalTree := .branch r212 r215
private abbrev r220 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 108
private theorem rc220 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449280 r220 = true := by decide +kernel

private abbrev r221 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 109
private theorem rc221 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449344 r221 = true := by decide +kernel

private def r219 : MobiusReciprocalTree := .branch r220 r221
private abbrev r223 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 110
private theorem rc223 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449408 r223 = true := by decide +kernel

private abbrev r224 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 111
private theorem rc224 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449472 r224 = true := by decide +kernel

private def r222 : MobiusReciprocalTree := .branch r223 r224
private def r218 : MobiusReciprocalTree := .branch r219 r222
private def r210 : MobiusReciprocalTree := .branch r211 r218
private def r194 : MobiusReciprocalTree := .branch r195 r210
private abbrev r229 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 112
private theorem rc229 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449536 r229 = true := by decide +kernel

private abbrev r230 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 113
private theorem rc230 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449600 r230 = true := by decide +kernel

private def r228 : MobiusReciprocalTree := .branch r229 r230
private abbrev r232 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 114
private theorem rc232 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449664 r232 = true := by decide +kernel

private abbrev r233 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 115
private theorem rc233 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449728 r233 = true := by decide +kernel

private def r231 : MobiusReciprocalTree := .branch r232 r233
private def r227 : MobiusReciprocalTree := .branch r228 r231
private abbrev r236 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 116
private theorem rc236 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449792 r236 = true := by decide +kernel

private abbrev r237 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 117
private theorem rc237 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449856 r237 = true := by decide +kernel

private def r235 : MobiusReciprocalTree := .branch r236 r237
private abbrev r239 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 118
private theorem rc239 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449920 r239 = true := by decide +kernel

private abbrev r240 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 119
private theorem rc240 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449984 r240 = true := by decide +kernel

private def r238 : MobiusReciprocalTree := .branch r239 r240
private def r234 : MobiusReciprocalTree := .branch r235 r238
private def r226 : MobiusReciprocalTree := .branch r227 r234
private abbrev r244 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 120
private theorem rc244 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450048 r244 = true := by decide +kernel

private abbrev r245 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 121
private theorem rc245 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450112 r245 = true := by decide +kernel

private def r243 : MobiusReciprocalTree := .branch r244 r245
private abbrev r247 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 122
private theorem rc247 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450176 r247 = true := by decide +kernel

private abbrev r248 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 123
private theorem rc248 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450240 r248 = true := by decide +kernel

private def r246 : MobiusReciprocalTree := .branch r247 r248
private def r242 : MobiusReciprocalTree := .branch r243 r246
private abbrev r251 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 124
private theorem rc251 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450304 r251 = true := by decide +kernel

private abbrev r252 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 125
private theorem rc252 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450368 r252 = true := by decide +kernel

private def r250 : MobiusReciprocalTree := .branch r251 r252
private abbrev r254 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 126
private theorem rc254 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450432 r254 = true := by decide +kernel

private abbrev r255 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block054 127
private theorem rc255 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450496 r255 = true := by decide +kernel

private def r253 : MobiusReciprocalTree := .branch r254 r255
private def r249 : MobiusReciprocalTree := .branch r250 r253
private def r241 : MobiusReciprocalTree := .branch r242 r249
private def r225 : MobiusReciprocalTree := .branch r226 r241
private def r193 : MobiusReciprocalTree := .branch r194 r225
private def r129 : MobiusReciprocalTree := .branch r130 r193
private def r1 : MobiusReciprocalTree := .branch r2 r129
private abbrev r263 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 0
private theorem rc263 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450560 r263 = true := by decide +kernel

private abbrev r264 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 1
private theorem rc264 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450624 r264 = true := by decide +kernel

private def r262 : MobiusReciprocalTree := .branch r263 r264
private abbrev r266 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 2
private theorem rc266 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450688 r266 = true := by decide +kernel

private abbrev r267 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 3
private theorem rc267 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450752 r267 = true := by decide +kernel

private def r265 : MobiusReciprocalTree := .branch r266 r267
private def r261 : MobiusReciprocalTree := .branch r262 r265
private abbrev r270 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 4
private theorem rc270 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450816 r270 = true := by decide +kernel

private abbrev r271 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 5
private theorem rc271 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450880 r271 = true := by decide +kernel

private def r269 : MobiusReciprocalTree := .branch r270 r271
private abbrev r273 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 6
private theorem rc273 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450944 r273 = true := by decide +kernel

private abbrev r274 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 7
private theorem rc274 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451008 r274 = true := by decide +kernel

private def r272 : MobiusReciprocalTree := .branch r273 r274
private def r268 : MobiusReciprocalTree := .branch r269 r272
private def r260 : MobiusReciprocalTree := .branch r261 r268
private abbrev r278 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 8
private theorem rc278 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451072 r278 = true := by decide +kernel

private abbrev r279 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 9
private theorem rc279 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451136 r279 = true := by decide +kernel

private def r277 : MobiusReciprocalTree := .branch r278 r279
private abbrev r281 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 10
private theorem rc281 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451200 r281 = true := by decide +kernel

private abbrev r282 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 11
private theorem rc282 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451264 r282 = true := by decide +kernel

private def r280 : MobiusReciprocalTree := .branch r281 r282
private def r276 : MobiusReciprocalTree := .branch r277 r280
private abbrev r285 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 12
private theorem rc285 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451328 r285 = true := by decide +kernel

private abbrev r286 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 13
private theorem rc286 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451392 r286 = true := by decide +kernel

private def r284 : MobiusReciprocalTree := .branch r285 r286
private abbrev r288 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 14
private theorem rc288 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451456 r288 = true := by decide +kernel

private abbrev r289 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 15
private theorem rc289 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451520 r289 = true := by decide +kernel

private def r287 : MobiusReciprocalTree := .branch r288 r289
private def r283 : MobiusReciprocalTree := .branch r284 r287
private def r275 : MobiusReciprocalTree := .branch r276 r283
private def r259 : MobiusReciprocalTree := .branch r260 r275
private abbrev r294 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 16
private theorem rc294 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451584 r294 = true := by decide +kernel

private abbrev r295 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 17
private theorem rc295 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451648 r295 = true := by decide +kernel

private def r293 : MobiusReciprocalTree := .branch r294 r295
private abbrev r297 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 18
private theorem rc297 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451712 r297 = true := by decide +kernel

private abbrev r298 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 19
private theorem rc298 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451776 r298 = true := by decide +kernel

private def r296 : MobiusReciprocalTree := .branch r297 r298
private def r292 : MobiusReciprocalTree := .branch r293 r296
private abbrev r301 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 20
private theorem rc301 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451840 r301 = true := by decide +kernel

private abbrev r302 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 21
private theorem rc302 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451904 r302 = true := by decide +kernel

private def r300 : MobiusReciprocalTree := .branch r301 r302
private abbrev r304 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 22
private theorem rc304 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451968 r304 = true := by decide +kernel

private abbrev r305 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 23
private theorem rc305 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452032 r305 = true := by decide +kernel

private def r303 : MobiusReciprocalTree := .branch r304 r305
private def r299 : MobiusReciprocalTree := .branch r300 r303
private def r291 : MobiusReciprocalTree := .branch r292 r299
private abbrev r309 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 24
private theorem rc309 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452096 r309 = true := by decide +kernel

private abbrev r310 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 25
private theorem rc310 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452160 r310 = true := by decide +kernel

private def r308 : MobiusReciprocalTree := .branch r309 r310
private abbrev r312 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 26
private theorem rc312 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452224 r312 = true := by decide +kernel

private abbrev r313 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 27
private theorem rc313 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452288 r313 = true := by decide +kernel

private def r311 : MobiusReciprocalTree := .branch r312 r313
private def r307 : MobiusReciprocalTree := .branch r308 r311
private abbrev r316 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 28
private theorem rc316 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452352 r316 = true := by decide +kernel

private abbrev r317 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 29
private theorem rc317 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452416 r317 = true := by decide +kernel

private def r315 : MobiusReciprocalTree := .branch r316 r317
private abbrev r319 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 30
private theorem rc319 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452480 r319 = true := by decide +kernel

private abbrev r320 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 31
private theorem rc320 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452544 r320 = true := by decide +kernel

private def r318 : MobiusReciprocalTree := .branch r319 r320
private def r314 : MobiusReciprocalTree := .branch r315 r318
private def r306 : MobiusReciprocalTree := .branch r307 r314
private def r290 : MobiusReciprocalTree := .branch r291 r306
private def r258 : MobiusReciprocalTree := .branch r259 r290
private abbrev r326 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 32
private theorem rc326 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452608 r326 = true := by decide +kernel

private abbrev r327 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 33
private theorem rc327 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452672 r327 = true := by decide +kernel

private def r325 : MobiusReciprocalTree := .branch r326 r327
private abbrev r329 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 34
private theorem rc329 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452736 r329 = true := by decide +kernel

private abbrev r330 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 35
private theorem rc330 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452800 r330 = true := by decide +kernel

private def r328 : MobiusReciprocalTree := .branch r329 r330
private def r324 : MobiusReciprocalTree := .branch r325 r328
private abbrev r333 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 36
private theorem rc333 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452864 r333 = true := by decide +kernel

private abbrev r334 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 37
private theorem rc334 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452928 r334 = true := by decide +kernel

private def r332 : MobiusReciprocalTree := .branch r333 r334
private abbrev r336 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 38
private theorem rc336 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452992 r336 = true := by decide +kernel

private abbrev r337 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 39
private theorem rc337 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453056 r337 = true := by decide +kernel

private def r335 : MobiusReciprocalTree := .branch r336 r337
private def r331 : MobiusReciprocalTree := .branch r332 r335
private def r323 : MobiusReciprocalTree := .branch r324 r331
private abbrev r341 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 40
private theorem rc341 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453120 r341 = true := by decide +kernel

private abbrev r342 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 41
private theorem rc342 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453184 r342 = true := by decide +kernel

private def r340 : MobiusReciprocalTree := .branch r341 r342
private abbrev r344 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 42
private theorem rc344 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453248 r344 = true := by decide +kernel

private abbrev r345 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 43
private theorem rc345 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453312 r345 = true := by decide +kernel

private def r343 : MobiusReciprocalTree := .branch r344 r345
private def r339 : MobiusReciprocalTree := .branch r340 r343
private abbrev r348 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 44
private theorem rc348 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453376 r348 = true := by decide +kernel

private abbrev r349 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 45
private theorem rc349 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453440 r349 = true := by decide +kernel

private def r347 : MobiusReciprocalTree := .branch r348 r349
private abbrev r351 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 46
private theorem rc351 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453504 r351 = true := by decide +kernel

private abbrev r352 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 47
private theorem rc352 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453568 r352 = true := by decide +kernel

private def r350 : MobiusReciprocalTree := .branch r351 r352
private def r346 : MobiusReciprocalTree := .branch r347 r350
private def r338 : MobiusReciprocalTree := .branch r339 r346
private def r322 : MobiusReciprocalTree := .branch r323 r338
private abbrev r357 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 48
private theorem rc357 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453632 r357 = true := by decide +kernel

private abbrev r358 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 49
private theorem rc358 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453696 r358 = true := by decide +kernel

private def r356 : MobiusReciprocalTree := .branch r357 r358
private abbrev r360 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 50
private theorem rc360 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453760 r360 = true := by decide +kernel

private abbrev r361 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 51
private theorem rc361 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453824 r361 = true := by decide +kernel

private def r359 : MobiusReciprocalTree := .branch r360 r361
private def r355 : MobiusReciprocalTree := .branch r356 r359
private abbrev r364 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 52
private theorem rc364 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453888 r364 = true := by decide +kernel

private abbrev r365 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 53
private theorem rc365 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453952 r365 = true := by decide +kernel

private def r363 : MobiusReciprocalTree := .branch r364 r365
private abbrev r367 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 54
private theorem rc367 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454016 r367 = true := by decide +kernel

private abbrev r368 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 55
private theorem rc368 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454080 r368 = true := by decide +kernel

private def r366 : MobiusReciprocalTree := .branch r367 r368
private def r362 : MobiusReciprocalTree := .branch r363 r366
private def r354 : MobiusReciprocalTree := .branch r355 r362
private abbrev r372 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 56
private theorem rc372 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454144 r372 = true := by decide +kernel

private abbrev r373 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 57
private theorem rc373 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454208 r373 = true := by decide +kernel

private def r371 : MobiusReciprocalTree := .branch r372 r373
private abbrev r375 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 58
private theorem rc375 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454272 r375 = true := by decide +kernel

private abbrev r376 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 59
private theorem rc376 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454336 r376 = true := by decide +kernel

private def r374 : MobiusReciprocalTree := .branch r375 r376
private def r370 : MobiusReciprocalTree := .branch r371 r374
private abbrev r379 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 60
private theorem rc379 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454400 r379 = true := by decide +kernel

private abbrev r380 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 61
private theorem rc380 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454464 r380 = true := by decide +kernel

private def r378 : MobiusReciprocalTree := .branch r379 r380
private abbrev r382 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 62
private theorem rc382 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454528 r382 = true := by decide +kernel

private abbrev r383 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 63
private theorem rc383 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454592 r383 = true := by decide +kernel

private def r381 : MobiusReciprocalTree := .branch r382 r383
private def r377 : MobiusReciprocalTree := .branch r378 r381
private def r369 : MobiusReciprocalTree := .branch r370 r377
private def r353 : MobiusReciprocalTree := .branch r354 r369
private def r321 : MobiusReciprocalTree := .branch r322 r353
private def r257 : MobiusReciprocalTree := .branch r258 r321
private abbrev r390 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 64
private theorem rc390 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454656 r390 = true := by decide +kernel

private abbrev r391 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 65
private theorem rc391 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454720 r391 = true := by decide +kernel

private def r389 : MobiusReciprocalTree := .branch r390 r391
private abbrev r393 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 66
private theorem rc393 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454784 r393 = true := by decide +kernel

private abbrev r394 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 67
private theorem rc394 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454848 r394 = true := by decide +kernel

private def r392 : MobiusReciprocalTree := .branch r393 r394
private def r388 : MobiusReciprocalTree := .branch r389 r392
private abbrev r397 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 68
private theorem rc397 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454912 r397 = true := by decide +kernel

private abbrev r398 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 69
private theorem rc398 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454976 r398 = true := by decide +kernel

private def r396 : MobiusReciprocalTree := .branch r397 r398
private abbrev r400 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 70
private theorem rc400 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455040 r400 = true := by decide +kernel

private abbrev r401 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 71
private theorem rc401 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455104 r401 = true := by decide +kernel

private def r399 : MobiusReciprocalTree := .branch r400 r401
private def r395 : MobiusReciprocalTree := .branch r396 r399
private def r387 : MobiusReciprocalTree := .branch r388 r395
private abbrev r405 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 72
private theorem rc405 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455168 r405 = true := by decide +kernel

private abbrev r406 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 73
private theorem rc406 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455232 r406 = true := by decide +kernel

private def r404 : MobiusReciprocalTree := .branch r405 r406
private abbrev r408 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 74
private theorem rc408 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455296 r408 = true := by decide +kernel

private abbrev r409 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 75
private theorem rc409 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455360 r409 = true := by decide +kernel

private def r407 : MobiusReciprocalTree := .branch r408 r409
private def r403 : MobiusReciprocalTree := .branch r404 r407
private abbrev r412 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 76
private theorem rc412 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455424 r412 = true := by decide +kernel

private abbrev r413 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 77
private theorem rc413 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455488 r413 = true := by decide +kernel

private def r411 : MobiusReciprocalTree := .branch r412 r413
private abbrev r415 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 78
private theorem rc415 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455552 r415 = true := by decide +kernel

private abbrev r416 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 79
private theorem rc416 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455616 r416 = true := by decide +kernel

private def r414 : MobiusReciprocalTree := .branch r415 r416
private def r410 : MobiusReciprocalTree := .branch r411 r414
private def r402 : MobiusReciprocalTree := .branch r403 r410
private def r386 : MobiusReciprocalTree := .branch r387 r402
private abbrev r421 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 80
private theorem rc421 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455680 r421 = true := by decide +kernel

private abbrev r422 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 81
private theorem rc422 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455744 r422 = true := by decide +kernel

private def r420 : MobiusReciprocalTree := .branch r421 r422
private abbrev r424 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 82
private theorem rc424 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455808 r424 = true := by decide +kernel

private abbrev r425 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 83
private theorem rc425 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455872 r425 = true := by decide +kernel

private def r423 : MobiusReciprocalTree := .branch r424 r425
private def r419 : MobiusReciprocalTree := .branch r420 r423
private abbrev r428 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 84
private theorem rc428 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455936 r428 = true := by decide +kernel

private abbrev r429 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 85
private theorem rc429 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456000 r429 = true := by decide +kernel

private def r427 : MobiusReciprocalTree := .branch r428 r429
private abbrev r431 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 86
private theorem rc431 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456064 r431 = true := by decide +kernel

private abbrev r432 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 87
private theorem rc432 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456128 r432 = true := by decide +kernel

private def r430 : MobiusReciprocalTree := .branch r431 r432
private def r426 : MobiusReciprocalTree := .branch r427 r430
private def r418 : MobiusReciprocalTree := .branch r419 r426
private abbrev r436 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 88
private theorem rc436 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456192 r436 = true := by decide +kernel

private abbrev r437 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 89
private theorem rc437 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456256 r437 = true := by decide +kernel

private def r435 : MobiusReciprocalTree := .branch r436 r437
private abbrev r439 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 90
private theorem rc439 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456320 r439 = true := by decide +kernel

private abbrev r440 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 91
private theorem rc440 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456384 r440 = true := by decide +kernel

private def r438 : MobiusReciprocalTree := .branch r439 r440
private def r434 : MobiusReciprocalTree := .branch r435 r438
private abbrev r443 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 92
private theorem rc443 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456448 r443 = true := by decide +kernel

private abbrev r444 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 93
private theorem rc444 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456512 r444 = true := by decide +kernel

private def r442 : MobiusReciprocalTree := .branch r443 r444
private abbrev r446 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 94
private theorem rc446 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456576 r446 = true := by decide +kernel

private abbrev r447 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 95
private theorem rc447 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456640 r447 = true := by decide +kernel

private def r445 : MobiusReciprocalTree := .branch r446 r447
private def r441 : MobiusReciprocalTree := .branch r442 r445
private def r433 : MobiusReciprocalTree := .branch r434 r441
private def r417 : MobiusReciprocalTree := .branch r418 r433
private def r385 : MobiusReciprocalTree := .branch r386 r417
private abbrev r453 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 96
private theorem rc453 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456704 r453 = true := by decide +kernel

private abbrev r454 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 97
private theorem rc454 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456768 r454 = true := by decide +kernel

private def r452 : MobiusReciprocalTree := .branch r453 r454
private abbrev r456 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 98
private theorem rc456 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456832 r456 = true := by decide +kernel

private abbrev r457 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 99
private theorem rc457 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456896 r457 = true := by decide +kernel

private def r455 : MobiusReciprocalTree := .branch r456 r457
private def r451 : MobiusReciprocalTree := .branch r452 r455
private abbrev r460 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 100
private theorem rc460 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456960 r460 = true := by decide +kernel

private abbrev r461 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 101
private theorem rc461 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457024 r461 = true := by decide +kernel

private def r459 : MobiusReciprocalTree := .branch r460 r461
private abbrev r463 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 102
private theorem rc463 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457088 r463 = true := by decide +kernel

private abbrev r464 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 103
private theorem rc464 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457152 r464 = true := by decide +kernel

private def r462 : MobiusReciprocalTree := .branch r463 r464
private def r458 : MobiusReciprocalTree := .branch r459 r462
private def r450 : MobiusReciprocalTree := .branch r451 r458
private abbrev r468 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 104
private theorem rc468 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457216 r468 = true := by decide +kernel

private abbrev r469 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 105
private theorem rc469 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457280 r469 = true := by decide +kernel

private def r467 : MobiusReciprocalTree := .branch r468 r469
private abbrev r471 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 106
private theorem rc471 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457344 r471 = true := by decide +kernel

private abbrev r472 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 107
private theorem rc472 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457408 r472 = true := by decide +kernel

private def r470 : MobiusReciprocalTree := .branch r471 r472
private def r466 : MobiusReciprocalTree := .branch r467 r470
private abbrev r475 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 108
private theorem rc475 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457472 r475 = true := by decide +kernel

private abbrev r476 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 109
private theorem rc476 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457536 r476 = true := by decide +kernel

private def r474 : MobiusReciprocalTree := .branch r475 r476
private abbrev r478 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 110
private theorem rc478 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457600 r478 = true := by decide +kernel

private abbrev r479 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 111
private theorem rc479 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457664 r479 = true := by decide +kernel

private def r477 : MobiusReciprocalTree := .branch r478 r479
private def r473 : MobiusReciprocalTree := .branch r474 r477
private def r465 : MobiusReciprocalTree := .branch r466 r473
private def r449 : MobiusReciprocalTree := .branch r450 r465
private abbrev r484 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 112
private theorem rc484 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457728 r484 = true := by decide +kernel

private abbrev r485 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 113
private theorem rc485 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457792 r485 = true := by decide +kernel

private def r483 : MobiusReciprocalTree := .branch r484 r485
private abbrev r487 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 114
private theorem rc487 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457856 r487 = true := by decide +kernel

private abbrev r488 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 115
private theorem rc488 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457920 r488 = true := by decide +kernel

private def r486 : MobiusReciprocalTree := .branch r487 r488
private def r482 : MobiusReciprocalTree := .branch r483 r486
private abbrev r491 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 116
private theorem rc491 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457984 r491 = true := by decide +kernel

private abbrev r492 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 117
private theorem rc492 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458048 r492 = true := by decide +kernel

private def r490 : MobiusReciprocalTree := .branch r491 r492
private abbrev r494 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 118
private theorem rc494 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458112 r494 = true := by decide +kernel

private abbrev r495 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 119
private theorem rc495 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458176 r495 = true := by decide +kernel

private def r493 : MobiusReciprocalTree := .branch r494 r495
private def r489 : MobiusReciprocalTree := .branch r490 r493
private def r481 : MobiusReciprocalTree := .branch r482 r489
private abbrev r499 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 120
private theorem rc499 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458240 r499 = true := by decide +kernel

private abbrev r500 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 121
private theorem rc500 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458304 r500 = true := by decide +kernel

private def r498 : MobiusReciprocalTree := .branch r499 r500
private abbrev r502 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 122
private theorem rc502 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458368 r502 = true := by decide +kernel

private abbrev r503 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 123
private theorem rc503 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458432 r503 = true := by decide +kernel

private def r501 : MobiusReciprocalTree := .branch r502 r503
private def r497 : MobiusReciprocalTree := .branch r498 r501
private abbrev r506 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 124
private theorem rc506 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458496 r506 = true := by decide +kernel

private abbrev r507 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 125
private theorem rc507 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458560 r507 = true := by decide +kernel

private def r505 : MobiusReciprocalTree := .branch r506 r507
private abbrev r509 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 126
private theorem rc509 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458624 r509 = true := by decide +kernel

private abbrev r510 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block055 127
private theorem rc510 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458688 r510 = true := by decide +kernel

private def r508 : MobiusReciprocalTree := .branch r509 r510
private def r504 : MobiusReciprocalTree := .branch r505 r508
private def r496 : MobiusReciprocalTree := .branch r497 r504
private def r480 : MobiusReciprocalTree := .branch r481 r496
private def r448 : MobiusReciprocalTree := .branch r449 r480
private def r384 : MobiusReciprocalTree := .branch r385 r448
private def r256 : MobiusReciprocalTree := .branch r257 r384
private def r0 : MobiusReciprocalTree := .branch r1 r256

theorem mobiusReciprocalPair027_checked_complete : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 442368 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block054 mobiusReciprocal1200001Block055) = true :=
  (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 8 442368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 7 442368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 442368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 442368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 442368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 442368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 442368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442368 _ _ (by decide) rc8 rc9 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442496 _ _ (by decide) rc11 rc12 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 442624 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442624 _ _ (by decide) rc15 rc16 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442752 _ _ (by decide) rc18 rc19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 442880 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 442880 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 442880 _ _ (by decide) rc23 rc24 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443008 _ _ (by decide) rc26 rc27 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 443136 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443136 _ _ (by decide) rc30 rc31 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443264 _ _ (by decide) rc33 rc34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 443392 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 443392 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 443392 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443392 _ _ (by decide) rc39 rc40 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443520 _ _ (by decide) rc42 rc43 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 443648 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443648 _ _ (by decide) rc46 rc47 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443776 _ _ (by decide) rc49 rc50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 443904 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 443904 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 443904 _ _ (by decide) rc54 rc55 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444032 _ _ (by decide) rc57 rc58 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 444160 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444160 _ _ (by decide) rc61 rc62 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444288 _ _ (by decide) rc64 rc65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 444416 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 444416 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 444416 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 444416 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444416 _ _ (by decide) rc71 rc72 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444544 _ _ (by decide) rc74 rc75 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 444672 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444672 _ _ (by decide) rc78 rc79 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444800 _ _ (by decide) rc81 rc82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 444928 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 444928 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 444928 _ _ (by decide) rc86 rc87 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445056 _ _ (by decide) rc89 rc90 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 445184 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445184 _ _ (by decide) rc93 rc94 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445312 _ _ (by decide) rc96 rc97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 445440 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 445440 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 445440 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445440 _ _ (by decide) rc102 rc103 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445568 _ _ (by decide) rc105 rc106 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 445696 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445696 _ _ (by decide) rc109 rc110 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445824 _ _ (by decide) rc112 rc113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 445952 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 445952 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 445952 _ _ (by decide) rc117 rc118 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446080 _ _ (by decide) rc120 rc121 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 446208 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446208 _ _ (by decide) rc124 rc125 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446336 _ _ (by decide) rc127 rc128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 446464 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 446464 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 446464 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 446464 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 446464 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446464 _ _ (by decide) rc135 rc136 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446592 _ _ (by decide) rc138 rc139 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 446720 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446720 _ _ (by decide) rc142 rc143 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446848 _ _ (by decide) rc145 rc146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 446976 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 446976 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 446976 _ _ (by decide) rc150 rc151 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447104 _ _ (by decide) rc153 rc154 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 447232 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447232 _ _ (by decide) rc157 rc158 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447360 _ _ (by decide) rc160 rc161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 447488 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 447488 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 447488 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447488 _ _ (by decide) rc166 rc167 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447616 _ _ (by decide) rc169 rc170 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 447744 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447744 _ _ (by decide) rc173 rc174 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 447872 _ _ (by decide) rc176 rc177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 448000 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 448000 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448000 _ _ (by decide) rc181 rc182 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448128 _ _ (by decide) rc184 rc185 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 448256 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448256 _ _ (by decide) rc188 rc189 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448384 _ _ (by decide) rc191 rc192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 448512 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 448512 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 448512 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 448512 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448512 _ _ (by decide) rc198 rc199 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448640 _ _ (by decide) rc201 rc202 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 448768 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448768 _ _ (by decide) rc205 rc206 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 448896 _ _ (by decide) rc208 rc209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 449024 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 449024 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449024 _ _ (by decide) rc213 rc214 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449152 _ _ (by decide) rc216 rc217 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 449280 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449280 _ _ (by decide) rc220 rc221 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449408 _ _ (by decide) rc223 rc224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 449536 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 449536 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 449536 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449536 _ _ (by decide) rc229 rc230 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449664 _ _ (by decide) rc232 rc233 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 449792 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449792 _ _ (by decide) rc236 rc237 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 449920 _ _ (by decide) rc239 rc240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 450048 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 450048 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450048 _ _ (by decide) rc244 rc245 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450176 _ _ (by decide) rc247 rc248 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 450304 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450304 _ _ (by decide) rc251 rc252 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450432 _ _ (by decide) rc254 rc255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 7 450560 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 450560 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 450560 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 450560 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 450560 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 450560 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450560 _ _ (by decide) rc263 rc264 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450688 _ _ (by decide) rc266 rc267 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 450816 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450816 _ _ (by decide) rc270 rc271 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 450944 _ _ (by decide) rc273 rc274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 451072 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 451072 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451072 _ _ (by decide) rc278 rc279 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451200 _ _ (by decide) rc281 rc282 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 451328 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451328 _ _ (by decide) rc285 rc286 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451456 _ _ (by decide) rc288 rc289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 451584 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 451584 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 451584 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451584 _ _ (by decide) rc294 rc295 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451712 _ _ (by decide) rc297 rc298 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 451840 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451840 _ _ (by decide) rc301 rc302 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 451968 _ _ (by decide) rc304 rc305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 452096 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 452096 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452096 _ _ (by decide) rc309 rc310 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452224 _ _ (by decide) rc312 rc313 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 452352 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452352 _ _ (by decide) rc316 rc317 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452480 _ _ (by decide) rc319 rc320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 452608 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 452608 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 452608 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 452608 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452608 _ _ (by decide) rc326 rc327 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452736 _ _ (by decide) rc329 rc330 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 452864 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452864 _ _ (by decide) rc333 rc334 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 452992 _ _ (by decide) rc336 rc337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 453120 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 453120 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453120 _ _ (by decide) rc341 rc342 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453248 _ _ (by decide) rc344 rc345 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 453376 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453376 _ _ (by decide) rc348 rc349 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453504 _ _ (by decide) rc351 rc352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 453632 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 453632 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 453632 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453632 _ _ (by decide) rc357 rc358 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453760 _ _ (by decide) rc360 rc361 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 453888 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 453888 _ _ (by decide) rc364 rc365 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454016 _ _ (by decide) rc367 rc368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 454144 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 454144 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454144 _ _ (by decide) rc372 rc373 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454272 _ _ (by decide) rc375 rc376 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 454400 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454400 _ _ (by decide) rc379 rc380 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454528 _ _ (by decide) rc382 rc383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 454656 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 454656 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 454656 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 454656 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 454656 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454656 _ _ (by decide) rc390 rc391 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454784 _ _ (by decide) rc393 rc394 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 454912 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 454912 _ _ (by decide) rc397 rc398 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455040 _ _ (by decide) rc400 rc401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 455168 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 455168 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455168 _ _ (by decide) rc405 rc406 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455296 _ _ (by decide) rc408 rc409 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 455424 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455424 _ _ (by decide) rc412 rc413 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455552 _ _ (by decide) rc415 rc416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 455680 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 455680 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 455680 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455680 _ _ (by decide) rc421 rc422 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455808 _ _ (by decide) rc424 rc425 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 455936 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 455936 _ _ (by decide) rc428 rc429 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456064 _ _ (by decide) rc431 rc432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 456192 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 456192 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456192 _ _ (by decide) rc436 rc437 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456320 _ _ (by decide) rc439 rc440 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 456448 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456448 _ _ (by decide) rc443 rc444 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456576 _ _ (by decide) rc446 rc447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 456704 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 456704 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 456704 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 456704 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456704 _ _ (by decide) rc453 rc454 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456832 _ _ (by decide) rc456 rc457 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 456960 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 456960 _ _ (by decide) rc460 rc461 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457088 _ _ (by decide) rc463 rc464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 457216 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 457216 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457216 _ _ (by decide) rc468 rc469 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457344 _ _ (by decide) rc471 rc472 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 457472 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457472 _ _ (by decide) rc475 rc476 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457600 _ _ (by decide) rc478 rc479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 457728 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 457728 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 457728 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457728 _ _ (by decide) rc484 rc485 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457856 _ _ (by decide) rc487 rc488 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 457984 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 457984 _ _ (by decide) rc491 rc492 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458112 _ _ (by decide) rc494 rc495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 458240 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 458240 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458240 _ _ (by decide) rc499 rc500 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458368 _ _ (by decide) rc502 rc503 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 458496 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458496 _ _ (by decide) rc506 rc507 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 458624 _ _ (by decide) rc509 rc510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott
end

open Helfgott
theorem solution : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 442368 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block054 mobiusReciprocal1200001Block055) = true := Helfgott.mobiusReciprocalPair027_checked_complete
#print axioms solution
