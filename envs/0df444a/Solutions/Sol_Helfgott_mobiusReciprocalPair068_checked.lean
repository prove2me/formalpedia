-- Prove2me | solution 1 for Helfgott.mobiusReciprocalPair068_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:45:12.261238+00:00
-- url     : https://prove2.me/submissions/f13f454a-ef7b-40a1-afe4-a7d905490bae

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part17
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

private abbrev r8 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 0
private theorem rc8 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114112 r8 = true := by decide +kernel

private abbrev r9 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 1
private theorem rc9 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114176 r9 = true := by decide +kernel

private def r7 : MobiusReciprocalTree := .branch r8 r9
private abbrev r11 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 2
private theorem rc11 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114240 r11 = true := by decide +kernel

private abbrev r12 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 3
private theorem rc12 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114304 r12 = true := by decide +kernel

private def r10 : MobiusReciprocalTree := .branch r11 r12
private def r6 : MobiusReciprocalTree := .branch r7 r10
private abbrev r15 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 4
private theorem rc15 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114368 r15 = true := by decide +kernel

private abbrev r16 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 5
private theorem rc16 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114432 r16 = true := by decide +kernel

private def r14 : MobiusReciprocalTree := .branch r15 r16
private abbrev r18 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 6
private theorem rc18 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114496 r18 = true := by decide +kernel

private abbrev r19 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 7
private theorem rc19 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114560 r19 = true := by decide +kernel

private def r17 : MobiusReciprocalTree := .branch r18 r19
private def r13 : MobiusReciprocalTree := .branch r14 r17
private def r5 : MobiusReciprocalTree := .branch r6 r13
private abbrev r23 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 8
private theorem rc23 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114624 r23 = true := by decide +kernel

private abbrev r24 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 9
private theorem rc24 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114688 r24 = true := by decide +kernel

private def r22 : MobiusReciprocalTree := .branch r23 r24
private abbrev r26 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 10
private theorem rc26 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114752 r26 = true := by decide +kernel

private abbrev r27 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 11
private theorem rc27 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114816 r27 = true := by decide +kernel

private def r25 : MobiusReciprocalTree := .branch r26 r27
private def r21 : MobiusReciprocalTree := .branch r22 r25
private abbrev r30 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 12
private theorem rc30 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114880 r30 = true := by decide +kernel

private abbrev r31 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 13
private theorem rc31 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114944 r31 = true := by decide +kernel

private def r29 : MobiusReciprocalTree := .branch r30 r31
private abbrev r33 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 14
private theorem rc33 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115008 r33 = true := by decide +kernel

private abbrev r34 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 15
private theorem rc34 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115072 r34 = true := by decide +kernel

private def r32 : MobiusReciprocalTree := .branch r33 r34
private def r28 : MobiusReciprocalTree := .branch r29 r32
private def r20 : MobiusReciprocalTree := .branch r21 r28
private def r4 : MobiusReciprocalTree := .branch r5 r20
private abbrev r39 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 16
private theorem rc39 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115136 r39 = true := by decide +kernel

private abbrev r40 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 17
private theorem rc40 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115200 r40 = true := by decide +kernel

private def r38 : MobiusReciprocalTree := .branch r39 r40
private abbrev r42 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 18
private theorem rc42 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115264 r42 = true := by decide +kernel

private abbrev r43 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 19
private theorem rc43 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115328 r43 = true := by decide +kernel

private def r41 : MobiusReciprocalTree := .branch r42 r43
private def r37 : MobiusReciprocalTree := .branch r38 r41
private abbrev r46 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 20
private theorem rc46 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115392 r46 = true := by decide +kernel

private abbrev r47 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 21
private theorem rc47 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115456 r47 = true := by decide +kernel

private def r45 : MobiusReciprocalTree := .branch r46 r47
private abbrev r49 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 22
private theorem rc49 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115520 r49 = true := by decide +kernel

private abbrev r50 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 23
private theorem rc50 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115584 r50 = true := by decide +kernel

private def r48 : MobiusReciprocalTree := .branch r49 r50
private def r44 : MobiusReciprocalTree := .branch r45 r48
private def r36 : MobiusReciprocalTree := .branch r37 r44
private abbrev r54 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 24
private theorem rc54 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115648 r54 = true := by decide +kernel

private abbrev r55 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 25
private theorem rc55 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115712 r55 = true := by decide +kernel

private def r53 : MobiusReciprocalTree := .branch r54 r55
private abbrev r57 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 26
private theorem rc57 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115776 r57 = true := by decide +kernel

private abbrev r58 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 27
private theorem rc58 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115840 r58 = true := by decide +kernel

private def r56 : MobiusReciprocalTree := .branch r57 r58
private def r52 : MobiusReciprocalTree := .branch r53 r56
private abbrev r61 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 28
private theorem rc61 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115904 r61 = true := by decide +kernel

private abbrev r62 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 29
private theorem rc62 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115968 r62 = true := by decide +kernel

private def r60 : MobiusReciprocalTree := .branch r61 r62
private abbrev r64 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 30
private theorem rc64 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116032 r64 = true := by decide +kernel

private abbrev r65 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 31
private theorem rc65 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116096 r65 = true := by decide +kernel

private def r63 : MobiusReciprocalTree := .branch r64 r65
private def r59 : MobiusReciprocalTree := .branch r60 r63
private def r51 : MobiusReciprocalTree := .branch r52 r59
private def r35 : MobiusReciprocalTree := .branch r36 r51
private def r3 : MobiusReciprocalTree := .branch r4 r35
private abbrev r71 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 32
private theorem rc71 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116160 r71 = true := by decide +kernel

private abbrev r72 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 33
private theorem rc72 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116224 r72 = true := by decide +kernel

private def r70 : MobiusReciprocalTree := .branch r71 r72
private abbrev r74 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 34
private theorem rc74 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116288 r74 = true := by decide +kernel

private abbrev r75 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 35
private theorem rc75 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116352 r75 = true := by decide +kernel

private def r73 : MobiusReciprocalTree := .branch r74 r75
private def r69 : MobiusReciprocalTree := .branch r70 r73
private abbrev r78 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 36
private theorem rc78 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116416 r78 = true := by decide +kernel

private abbrev r79 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 37
private theorem rc79 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116480 r79 = true := by decide +kernel

private def r77 : MobiusReciprocalTree := .branch r78 r79
private abbrev r81 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 38
private theorem rc81 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116544 r81 = true := by decide +kernel

private abbrev r82 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 39
private theorem rc82 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116608 r82 = true := by decide +kernel

private def r80 : MobiusReciprocalTree := .branch r81 r82
private def r76 : MobiusReciprocalTree := .branch r77 r80
private def r68 : MobiusReciprocalTree := .branch r69 r76
private abbrev r86 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 40
private theorem rc86 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116672 r86 = true := by decide +kernel

private abbrev r87 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 41
private theorem rc87 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116736 r87 = true := by decide +kernel

private def r85 : MobiusReciprocalTree := .branch r86 r87
private abbrev r89 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 42
private theorem rc89 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116800 r89 = true := by decide +kernel

private abbrev r90 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 43
private theorem rc90 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116864 r90 = true := by decide +kernel

private def r88 : MobiusReciprocalTree := .branch r89 r90
private def r84 : MobiusReciprocalTree := .branch r85 r88
private abbrev r93 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 44
private theorem rc93 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116928 r93 = true := by decide +kernel

private abbrev r94 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 45
private theorem rc94 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116992 r94 = true := by decide +kernel

private def r92 : MobiusReciprocalTree := .branch r93 r94
private abbrev r96 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 46
private theorem rc96 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117056 r96 = true := by decide +kernel

private abbrev r97 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 47
private theorem rc97 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117120 r97 = true := by decide +kernel

private def r95 : MobiusReciprocalTree := .branch r96 r97
private def r91 : MobiusReciprocalTree := .branch r92 r95
private def r83 : MobiusReciprocalTree := .branch r84 r91
private def r67 : MobiusReciprocalTree := .branch r68 r83
private abbrev r102 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 48
private theorem rc102 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117184 r102 = true := by decide +kernel

private abbrev r103 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 49
private theorem rc103 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117248 r103 = true := by decide +kernel

private def r101 : MobiusReciprocalTree := .branch r102 r103
private abbrev r105 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 50
private theorem rc105 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117312 r105 = true := by decide +kernel

private abbrev r106 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 51
private theorem rc106 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117376 r106 = true := by decide +kernel

private def r104 : MobiusReciprocalTree := .branch r105 r106
private def r100 : MobiusReciprocalTree := .branch r101 r104
private abbrev r109 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 52
private theorem rc109 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117440 r109 = true := by decide +kernel

private abbrev r110 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 53
private theorem rc110 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117504 r110 = true := by decide +kernel

private def r108 : MobiusReciprocalTree := .branch r109 r110
private abbrev r112 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 54
private theorem rc112 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117568 r112 = true := by decide +kernel

private abbrev r113 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 55
private theorem rc113 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117632 r113 = true := by decide +kernel

private def r111 : MobiusReciprocalTree := .branch r112 r113
private def r107 : MobiusReciprocalTree := .branch r108 r111
private def r99 : MobiusReciprocalTree := .branch r100 r107
private abbrev r117 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 56
private theorem rc117 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117696 r117 = true := by decide +kernel

private abbrev r118 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 57
private theorem rc118 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117760 r118 = true := by decide +kernel

private def r116 : MobiusReciprocalTree := .branch r117 r118
private abbrev r120 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 58
private theorem rc120 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117824 r120 = true := by decide +kernel

private abbrev r121 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 59
private theorem rc121 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117888 r121 = true := by decide +kernel

private def r119 : MobiusReciprocalTree := .branch r120 r121
private def r115 : MobiusReciprocalTree := .branch r116 r119
private abbrev r124 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 60
private theorem rc124 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117952 r124 = true := by decide +kernel

private abbrev r125 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 61
private theorem rc125 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118016 r125 = true := by decide +kernel

private def r123 : MobiusReciprocalTree := .branch r124 r125
private abbrev r127 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 62
private theorem rc127 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118080 r127 = true := by decide +kernel

private abbrev r128 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 63
private theorem rc128 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118144 r128 = true := by decide +kernel

private def r126 : MobiusReciprocalTree := .branch r127 r128
private def r122 : MobiusReciprocalTree := .branch r123 r126
private def r114 : MobiusReciprocalTree := .branch r115 r122
private def r98 : MobiusReciprocalTree := .branch r99 r114
private def r66 : MobiusReciprocalTree := .branch r67 r98
private def r2 : MobiusReciprocalTree := .branch r3 r66
private abbrev r135 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 64
private theorem rc135 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118208 r135 = true := by decide +kernel

private abbrev r136 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 65
private theorem rc136 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118272 r136 = true := by decide +kernel

private def r134 : MobiusReciprocalTree := .branch r135 r136
private abbrev r138 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 66
private theorem rc138 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118336 r138 = true := by decide +kernel

private abbrev r139 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 67
private theorem rc139 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118400 r139 = true := by decide +kernel

private def r137 : MobiusReciprocalTree := .branch r138 r139
private def r133 : MobiusReciprocalTree := .branch r134 r137
private abbrev r142 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 68
private theorem rc142 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118464 r142 = true := by decide +kernel

private abbrev r143 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 69
private theorem rc143 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118528 r143 = true := by decide +kernel

private def r141 : MobiusReciprocalTree := .branch r142 r143
private abbrev r145 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 70
private theorem rc145 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118592 r145 = true := by decide +kernel

private abbrev r146 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 71
private theorem rc146 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118656 r146 = true := by decide +kernel

private def r144 : MobiusReciprocalTree := .branch r145 r146
private def r140 : MobiusReciprocalTree := .branch r141 r144
private def r132 : MobiusReciprocalTree := .branch r133 r140
private abbrev r150 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 72
private theorem rc150 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118720 r150 = true := by decide +kernel

private abbrev r151 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 73
private theorem rc151 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118784 r151 = true := by decide +kernel

private def r149 : MobiusReciprocalTree := .branch r150 r151
private abbrev r153 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 74
private theorem rc153 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118848 r153 = true := by decide +kernel

private abbrev r154 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 75
private theorem rc154 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118912 r154 = true := by decide +kernel

private def r152 : MobiusReciprocalTree := .branch r153 r154
private def r148 : MobiusReciprocalTree := .branch r149 r152
private abbrev r157 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 76
private theorem rc157 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118976 r157 = true := by decide +kernel

private abbrev r158 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 77
private theorem rc158 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119040 r158 = true := by decide +kernel

private def r156 : MobiusReciprocalTree := .branch r157 r158
private abbrev r160 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 78
private theorem rc160 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119104 r160 = true := by decide +kernel

private abbrev r161 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 79
private theorem rc161 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119168 r161 = true := by decide +kernel

private def r159 : MobiusReciprocalTree := .branch r160 r161
private def r155 : MobiusReciprocalTree := .branch r156 r159
private def r147 : MobiusReciprocalTree := .branch r148 r155
private def r131 : MobiusReciprocalTree := .branch r132 r147
private abbrev r166 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 80
private theorem rc166 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119232 r166 = true := by decide +kernel

private abbrev r167 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 81
private theorem rc167 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119296 r167 = true := by decide +kernel

private def r165 : MobiusReciprocalTree := .branch r166 r167
private abbrev r169 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 82
private theorem rc169 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119360 r169 = true := by decide +kernel

private abbrev r170 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 83
private theorem rc170 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119424 r170 = true := by decide +kernel

private def r168 : MobiusReciprocalTree := .branch r169 r170
private def r164 : MobiusReciprocalTree := .branch r165 r168
private abbrev r173 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 84
private theorem rc173 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119488 r173 = true := by decide +kernel

private abbrev r174 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 85
private theorem rc174 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119552 r174 = true := by decide +kernel

private def r172 : MobiusReciprocalTree := .branch r173 r174
private abbrev r176 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 86
private theorem rc176 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119616 r176 = true := by decide +kernel

private abbrev r177 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 87
private theorem rc177 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119680 r177 = true := by decide +kernel

private def r175 : MobiusReciprocalTree := .branch r176 r177
private def r171 : MobiusReciprocalTree := .branch r172 r175
private def r163 : MobiusReciprocalTree := .branch r164 r171
private abbrev r181 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 88
private theorem rc181 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119744 r181 = true := by decide +kernel

private abbrev r182 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 89
private theorem rc182 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119808 r182 = true := by decide +kernel

private def r180 : MobiusReciprocalTree := .branch r181 r182
private abbrev r184 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 90
private theorem rc184 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119872 r184 = true := by decide +kernel

private abbrev r185 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 91
private theorem rc185 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119936 r185 = true := by decide +kernel

private def r183 : MobiusReciprocalTree := .branch r184 r185
private def r179 : MobiusReciprocalTree := .branch r180 r183
private abbrev r188 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 92
private theorem rc188 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120000 r188 = true := by decide +kernel

private abbrev r189 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 93
private theorem rc189 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120064 r189 = true := by decide +kernel

private def r187 : MobiusReciprocalTree := .branch r188 r189
private abbrev r191 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 94
private theorem rc191 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120128 r191 = true := by decide +kernel

private abbrev r192 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 95
private theorem rc192 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120192 r192 = true := by decide +kernel

private def r190 : MobiusReciprocalTree := .branch r191 r192
private def r186 : MobiusReciprocalTree := .branch r187 r190
private def r178 : MobiusReciprocalTree := .branch r179 r186
private def r162 : MobiusReciprocalTree := .branch r163 r178
private def r130 : MobiusReciprocalTree := .branch r131 r162
private abbrev r198 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 96
private theorem rc198 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120256 r198 = true := by decide +kernel

private abbrev r199 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 97
private theorem rc199 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120320 r199 = true := by decide +kernel

private def r197 : MobiusReciprocalTree := .branch r198 r199
private abbrev r201 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 98
private theorem rc201 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120384 r201 = true := by decide +kernel

private abbrev r202 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 99
private theorem rc202 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120448 r202 = true := by decide +kernel

private def r200 : MobiusReciprocalTree := .branch r201 r202
private def r196 : MobiusReciprocalTree := .branch r197 r200
private abbrev r205 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 100
private theorem rc205 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120512 r205 = true := by decide +kernel

private abbrev r206 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 101
private theorem rc206 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120576 r206 = true := by decide +kernel

private def r204 : MobiusReciprocalTree := .branch r205 r206
private abbrev r208 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 102
private theorem rc208 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120640 r208 = true := by decide +kernel

private abbrev r209 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 103
private theorem rc209 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120704 r209 = true := by decide +kernel

private def r207 : MobiusReciprocalTree := .branch r208 r209
private def r203 : MobiusReciprocalTree := .branch r204 r207
private def r195 : MobiusReciprocalTree := .branch r196 r203
private abbrev r213 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 104
private theorem rc213 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120768 r213 = true := by decide +kernel

private abbrev r214 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 105
private theorem rc214 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120832 r214 = true := by decide +kernel

private def r212 : MobiusReciprocalTree := .branch r213 r214
private abbrev r216 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 106
private theorem rc216 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120896 r216 = true := by decide +kernel

private abbrev r217 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 107
private theorem rc217 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120960 r217 = true := by decide +kernel

private def r215 : MobiusReciprocalTree := .branch r216 r217
private def r211 : MobiusReciprocalTree := .branch r212 r215
private abbrev r220 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 108
private theorem rc220 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121024 r220 = true := by decide +kernel

private abbrev r221 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 109
private theorem rc221 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121088 r221 = true := by decide +kernel

private def r219 : MobiusReciprocalTree := .branch r220 r221
private abbrev r223 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 110
private theorem rc223 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121152 r223 = true := by decide +kernel

private abbrev r224 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 111
private theorem rc224 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121216 r224 = true := by decide +kernel

private def r222 : MobiusReciprocalTree := .branch r223 r224
private def r218 : MobiusReciprocalTree := .branch r219 r222
private def r210 : MobiusReciprocalTree := .branch r211 r218
private def r194 : MobiusReciprocalTree := .branch r195 r210
private abbrev r229 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 112
private theorem rc229 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121280 r229 = true := by decide +kernel

private abbrev r230 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 113
private theorem rc230 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121344 r230 = true := by decide +kernel

private def r228 : MobiusReciprocalTree := .branch r229 r230
private abbrev r232 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 114
private theorem rc232 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121408 r232 = true := by decide +kernel

private abbrev r233 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 115
private theorem rc233 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121472 r233 = true := by decide +kernel

private def r231 : MobiusReciprocalTree := .branch r232 r233
private def r227 : MobiusReciprocalTree := .branch r228 r231
private abbrev r236 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 116
private theorem rc236 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121536 r236 = true := by decide +kernel

private abbrev r237 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 117
private theorem rc237 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121600 r237 = true := by decide +kernel

private def r235 : MobiusReciprocalTree := .branch r236 r237
private abbrev r239 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 118
private theorem rc239 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121664 r239 = true := by decide +kernel

private abbrev r240 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 119
private theorem rc240 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121728 r240 = true := by decide +kernel

private def r238 : MobiusReciprocalTree := .branch r239 r240
private def r234 : MobiusReciprocalTree := .branch r235 r238
private def r226 : MobiusReciprocalTree := .branch r227 r234
private abbrev r244 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 120
private theorem rc244 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121792 r244 = true := by decide +kernel

private abbrev r245 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 121
private theorem rc245 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121856 r245 = true := by decide +kernel

private def r243 : MobiusReciprocalTree := .branch r244 r245
private abbrev r247 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 122
private theorem rc247 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121920 r247 = true := by decide +kernel

private abbrev r248 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 123
private theorem rc248 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121984 r248 = true := by decide +kernel

private def r246 : MobiusReciprocalTree := .branch r247 r248
private def r242 : MobiusReciprocalTree := .branch r243 r246
private abbrev r251 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 124
private theorem rc251 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122048 r251 = true := by decide +kernel

private abbrev r252 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 125
private theorem rc252 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122112 r252 = true := by decide +kernel

private def r250 : MobiusReciprocalTree := .branch r251 r252
private abbrev r254 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 126
private theorem rc254 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122176 r254 = true := by decide +kernel

private abbrev r255 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block136 127
private theorem rc255 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122240 r255 = true := by decide +kernel

private def r253 : MobiusReciprocalTree := .branch r254 r255
private def r249 : MobiusReciprocalTree := .branch r250 r253
private def r241 : MobiusReciprocalTree := .branch r242 r249
private def r225 : MobiusReciprocalTree := .branch r226 r241
private def r193 : MobiusReciprocalTree := .branch r194 r225
private def r129 : MobiusReciprocalTree := .branch r130 r193
private def r1 : MobiusReciprocalTree := .branch r2 r129
private abbrev r263 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 0
private theorem rc263 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122304 r263 = true := by decide +kernel

private abbrev r264 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 1
private theorem rc264 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122368 r264 = true := by decide +kernel

private def r262 : MobiusReciprocalTree := .branch r263 r264
private abbrev r266 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 2
private theorem rc266 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122432 r266 = true := by decide +kernel

private abbrev r267 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 3
private theorem rc267 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122496 r267 = true := by decide +kernel

private def r265 : MobiusReciprocalTree := .branch r266 r267
private def r261 : MobiusReciprocalTree := .branch r262 r265
private abbrev r270 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 4
private theorem rc270 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122560 r270 = true := by decide +kernel

private abbrev r271 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 5
private theorem rc271 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122624 r271 = true := by decide +kernel

private def r269 : MobiusReciprocalTree := .branch r270 r271
private abbrev r273 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 6
private theorem rc273 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122688 r273 = true := by decide +kernel

private abbrev r274 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 7
private theorem rc274 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122752 r274 = true := by decide +kernel

private def r272 : MobiusReciprocalTree := .branch r273 r274
private def r268 : MobiusReciprocalTree := .branch r269 r272
private def r260 : MobiusReciprocalTree := .branch r261 r268
private abbrev r278 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 8
private theorem rc278 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122816 r278 = true := by decide +kernel

private abbrev r279 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 9
private theorem rc279 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122880 r279 = true := by decide +kernel

private def r277 : MobiusReciprocalTree := .branch r278 r279
private abbrev r281 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 10
private theorem rc281 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122944 r281 = true := by decide +kernel

private abbrev r282 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 11
private theorem rc282 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123008 r282 = true := by decide +kernel

private def r280 : MobiusReciprocalTree := .branch r281 r282
private def r276 : MobiusReciprocalTree := .branch r277 r280
private abbrev r285 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 12
private theorem rc285 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123072 r285 = true := by decide +kernel

private abbrev r286 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 13
private theorem rc286 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123136 r286 = true := by decide +kernel

private def r284 : MobiusReciprocalTree := .branch r285 r286
private abbrev r288 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 14
private theorem rc288 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123200 r288 = true := by decide +kernel

private abbrev r289 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 15
private theorem rc289 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123264 r289 = true := by decide +kernel

private def r287 : MobiusReciprocalTree := .branch r288 r289
private def r283 : MobiusReciprocalTree := .branch r284 r287
private def r275 : MobiusReciprocalTree := .branch r276 r283
private def r259 : MobiusReciprocalTree := .branch r260 r275
private abbrev r294 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 16
private theorem rc294 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123328 r294 = true := by decide +kernel

private abbrev r295 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 17
private theorem rc295 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123392 r295 = true := by decide +kernel

private def r293 : MobiusReciprocalTree := .branch r294 r295
private abbrev r297 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 18
private theorem rc297 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123456 r297 = true := by decide +kernel

private abbrev r298 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 19
private theorem rc298 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123520 r298 = true := by decide +kernel

private def r296 : MobiusReciprocalTree := .branch r297 r298
private def r292 : MobiusReciprocalTree := .branch r293 r296
private abbrev r301 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 20
private theorem rc301 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123584 r301 = true := by decide +kernel

private abbrev r302 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 21
private theorem rc302 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123648 r302 = true := by decide +kernel

private def r300 : MobiusReciprocalTree := .branch r301 r302
private abbrev r304 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 22
private theorem rc304 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123712 r304 = true := by decide +kernel

private abbrev r305 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 23
private theorem rc305 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123776 r305 = true := by decide +kernel

private def r303 : MobiusReciprocalTree := .branch r304 r305
private def r299 : MobiusReciprocalTree := .branch r300 r303
private def r291 : MobiusReciprocalTree := .branch r292 r299
private abbrev r309 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 24
private theorem rc309 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123840 r309 = true := by decide +kernel

private abbrev r310 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 25
private theorem rc310 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123904 r310 = true := by decide +kernel

private def r308 : MobiusReciprocalTree := .branch r309 r310
private abbrev r312 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 26
private theorem rc312 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123968 r312 = true := by decide +kernel

private abbrev r313 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 27
private theorem rc313 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124032 r313 = true := by decide +kernel

private def r311 : MobiusReciprocalTree := .branch r312 r313
private def r307 : MobiusReciprocalTree := .branch r308 r311
private abbrev r316 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 28
private theorem rc316 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124096 r316 = true := by decide +kernel

private abbrev r317 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 29
private theorem rc317 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124160 r317 = true := by decide +kernel

private def r315 : MobiusReciprocalTree := .branch r316 r317
private abbrev r319 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 30
private theorem rc319 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124224 r319 = true := by decide +kernel

private abbrev r320 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 31
private theorem rc320 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124288 r320 = true := by decide +kernel

private def r318 : MobiusReciprocalTree := .branch r319 r320
private def r314 : MobiusReciprocalTree := .branch r315 r318
private def r306 : MobiusReciprocalTree := .branch r307 r314
private def r290 : MobiusReciprocalTree := .branch r291 r306
private def r258 : MobiusReciprocalTree := .branch r259 r290
private abbrev r326 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 32
private theorem rc326 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124352 r326 = true := by decide +kernel

private abbrev r327 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 33
private theorem rc327 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124416 r327 = true := by decide +kernel

private def r325 : MobiusReciprocalTree := .branch r326 r327
private abbrev r329 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 34
private theorem rc329 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124480 r329 = true := by decide +kernel

private abbrev r330 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 35
private theorem rc330 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124544 r330 = true := by decide +kernel

private def r328 : MobiusReciprocalTree := .branch r329 r330
private def r324 : MobiusReciprocalTree := .branch r325 r328
private abbrev r333 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 36
private theorem rc333 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124608 r333 = true := by decide +kernel

private abbrev r334 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 37
private theorem rc334 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124672 r334 = true := by decide +kernel

private def r332 : MobiusReciprocalTree := .branch r333 r334
private abbrev r336 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 38
private theorem rc336 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124736 r336 = true := by decide +kernel

private abbrev r337 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 39
private theorem rc337 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124800 r337 = true := by decide +kernel

private def r335 : MobiusReciprocalTree := .branch r336 r337
private def r331 : MobiusReciprocalTree := .branch r332 r335
private def r323 : MobiusReciprocalTree := .branch r324 r331
private abbrev r341 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 40
private theorem rc341 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124864 r341 = true := by decide +kernel

private abbrev r342 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 41
private theorem rc342 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124928 r342 = true := by decide +kernel

private def r340 : MobiusReciprocalTree := .branch r341 r342
private abbrev r344 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 42
private theorem rc344 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124992 r344 = true := by decide +kernel

private abbrev r345 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 43
private theorem rc345 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125056 r345 = true := by decide +kernel

private def r343 : MobiusReciprocalTree := .branch r344 r345
private def r339 : MobiusReciprocalTree := .branch r340 r343
private abbrev r348 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 44
private theorem rc348 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125120 r348 = true := by decide +kernel

private abbrev r349 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 45
private theorem rc349 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125184 r349 = true := by decide +kernel

private def r347 : MobiusReciprocalTree := .branch r348 r349
private abbrev r351 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 46
private theorem rc351 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125248 r351 = true := by decide +kernel

private abbrev r352 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 47
private theorem rc352 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125312 r352 = true := by decide +kernel

private def r350 : MobiusReciprocalTree := .branch r351 r352
private def r346 : MobiusReciprocalTree := .branch r347 r350
private def r338 : MobiusReciprocalTree := .branch r339 r346
private def r322 : MobiusReciprocalTree := .branch r323 r338
private abbrev r357 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 48
private theorem rc357 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125376 r357 = true := by decide +kernel

private abbrev r358 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 49
private theorem rc358 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125440 r358 = true := by decide +kernel

private def r356 : MobiusReciprocalTree := .branch r357 r358
private abbrev r360 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 50
private theorem rc360 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125504 r360 = true := by decide +kernel

private abbrev r361 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 51
private theorem rc361 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125568 r361 = true := by decide +kernel

private def r359 : MobiusReciprocalTree := .branch r360 r361
private def r355 : MobiusReciprocalTree := .branch r356 r359
private abbrev r364 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 52
private theorem rc364 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125632 r364 = true := by decide +kernel

private abbrev r365 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 53
private theorem rc365 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125696 r365 = true := by decide +kernel

private def r363 : MobiusReciprocalTree := .branch r364 r365
private abbrev r367 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 54
private theorem rc367 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125760 r367 = true := by decide +kernel

private abbrev r368 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 55
private theorem rc368 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125824 r368 = true := by decide +kernel

private def r366 : MobiusReciprocalTree := .branch r367 r368
private def r362 : MobiusReciprocalTree := .branch r363 r366
private def r354 : MobiusReciprocalTree := .branch r355 r362
private abbrev r372 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 56
private theorem rc372 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125888 r372 = true := by decide +kernel

private abbrev r373 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 57
private theorem rc373 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125952 r373 = true := by decide +kernel

private def r371 : MobiusReciprocalTree := .branch r372 r373
private abbrev r375 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 58
private theorem rc375 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126016 r375 = true := by decide +kernel

private abbrev r376 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 59
private theorem rc376 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126080 r376 = true := by decide +kernel

private def r374 : MobiusReciprocalTree := .branch r375 r376
private def r370 : MobiusReciprocalTree := .branch r371 r374
private abbrev r379 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 60
private theorem rc379 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126144 r379 = true := by decide +kernel

private abbrev r380 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 61
private theorem rc380 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126208 r380 = true := by decide +kernel

private def r378 : MobiusReciprocalTree := .branch r379 r380
private abbrev r382 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 62
private theorem rc382 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126272 r382 = true := by decide +kernel

private abbrev r383 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 63
private theorem rc383 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126336 r383 = true := by decide +kernel

private def r381 : MobiusReciprocalTree := .branch r382 r383
private def r377 : MobiusReciprocalTree := .branch r378 r381
private def r369 : MobiusReciprocalTree := .branch r370 r377
private def r353 : MobiusReciprocalTree := .branch r354 r369
private def r321 : MobiusReciprocalTree := .branch r322 r353
private def r257 : MobiusReciprocalTree := .branch r258 r321
private abbrev r390 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 64
private theorem rc390 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126400 r390 = true := by decide +kernel

private abbrev r391 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 65
private theorem rc391 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126464 r391 = true := by decide +kernel

private def r389 : MobiusReciprocalTree := .branch r390 r391
private abbrev r393 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 66
private theorem rc393 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126528 r393 = true := by decide +kernel

private abbrev r394 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 67
private theorem rc394 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126592 r394 = true := by decide +kernel

private def r392 : MobiusReciprocalTree := .branch r393 r394
private def r388 : MobiusReciprocalTree := .branch r389 r392
private abbrev r397 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 68
private theorem rc397 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126656 r397 = true := by decide +kernel

private abbrev r398 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 69
private theorem rc398 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126720 r398 = true := by decide +kernel

private def r396 : MobiusReciprocalTree := .branch r397 r398
private abbrev r400 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 70
private theorem rc400 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126784 r400 = true := by decide +kernel

private abbrev r401 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 71
private theorem rc401 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126848 r401 = true := by decide +kernel

private def r399 : MobiusReciprocalTree := .branch r400 r401
private def r395 : MobiusReciprocalTree := .branch r396 r399
private def r387 : MobiusReciprocalTree := .branch r388 r395
private abbrev r405 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 72
private theorem rc405 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126912 r405 = true := by decide +kernel

private abbrev r406 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 73
private theorem rc406 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126976 r406 = true := by decide +kernel

private def r404 : MobiusReciprocalTree := .branch r405 r406
private abbrev r408 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 74
private theorem rc408 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127040 r408 = true := by decide +kernel

private abbrev r409 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 75
private theorem rc409 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127104 r409 = true := by decide +kernel

private def r407 : MobiusReciprocalTree := .branch r408 r409
private def r403 : MobiusReciprocalTree := .branch r404 r407
private abbrev r412 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 76
private theorem rc412 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127168 r412 = true := by decide +kernel

private abbrev r413 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 77
private theorem rc413 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127232 r413 = true := by decide +kernel

private def r411 : MobiusReciprocalTree := .branch r412 r413
private abbrev r415 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 78
private theorem rc415 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127296 r415 = true := by decide +kernel

private abbrev r416 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 79
private theorem rc416 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127360 r416 = true := by decide +kernel

private def r414 : MobiusReciprocalTree := .branch r415 r416
private def r410 : MobiusReciprocalTree := .branch r411 r414
private def r402 : MobiusReciprocalTree := .branch r403 r410
private def r386 : MobiusReciprocalTree := .branch r387 r402
private abbrev r421 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 80
private theorem rc421 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127424 r421 = true := by decide +kernel

private abbrev r422 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 81
private theorem rc422 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127488 r422 = true := by decide +kernel

private def r420 : MobiusReciprocalTree := .branch r421 r422
private abbrev r424 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 82
private theorem rc424 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127552 r424 = true := by decide +kernel

private abbrev r425 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 83
private theorem rc425 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127616 r425 = true := by decide +kernel

private def r423 : MobiusReciprocalTree := .branch r424 r425
private def r419 : MobiusReciprocalTree := .branch r420 r423
private abbrev r428 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 84
private theorem rc428 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127680 r428 = true := by decide +kernel

private abbrev r429 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 85
private theorem rc429 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127744 r429 = true := by decide +kernel

private def r427 : MobiusReciprocalTree := .branch r428 r429
private abbrev r431 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 86
private theorem rc431 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127808 r431 = true := by decide +kernel

private abbrev r432 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 87
private theorem rc432 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127872 r432 = true := by decide +kernel

private def r430 : MobiusReciprocalTree := .branch r431 r432
private def r426 : MobiusReciprocalTree := .branch r427 r430
private def r418 : MobiusReciprocalTree := .branch r419 r426
private abbrev r436 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 88
private theorem rc436 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127936 r436 = true := by decide +kernel

private abbrev r437 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 89
private theorem rc437 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128000 r437 = true := by decide +kernel

private def r435 : MobiusReciprocalTree := .branch r436 r437
private abbrev r439 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 90
private theorem rc439 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128064 r439 = true := by decide +kernel

private abbrev r440 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 91
private theorem rc440 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128128 r440 = true := by decide +kernel

private def r438 : MobiusReciprocalTree := .branch r439 r440
private def r434 : MobiusReciprocalTree := .branch r435 r438
private abbrev r443 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 92
private theorem rc443 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128192 r443 = true := by decide +kernel

private abbrev r444 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 93
private theorem rc444 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128256 r444 = true := by decide +kernel

private def r442 : MobiusReciprocalTree := .branch r443 r444
private abbrev r446 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 94
private theorem rc446 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128320 r446 = true := by decide +kernel

private abbrev r447 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 95
private theorem rc447 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128384 r447 = true := by decide +kernel

private def r445 : MobiusReciprocalTree := .branch r446 r447
private def r441 : MobiusReciprocalTree := .branch r442 r445
private def r433 : MobiusReciprocalTree := .branch r434 r441
private def r417 : MobiusReciprocalTree := .branch r418 r433
private def r385 : MobiusReciprocalTree := .branch r386 r417
private abbrev r453 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 96
private theorem rc453 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128448 r453 = true := by decide +kernel

private abbrev r454 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 97
private theorem rc454 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128512 r454 = true := by decide +kernel

private def r452 : MobiusReciprocalTree := .branch r453 r454
private abbrev r456 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 98
private theorem rc456 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128576 r456 = true := by decide +kernel

private abbrev r457 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 99
private theorem rc457 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128640 r457 = true := by decide +kernel

private def r455 : MobiusReciprocalTree := .branch r456 r457
private def r451 : MobiusReciprocalTree := .branch r452 r455
private abbrev r460 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 100
private theorem rc460 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128704 r460 = true := by decide +kernel

private abbrev r461 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 101
private theorem rc461 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128768 r461 = true := by decide +kernel

private def r459 : MobiusReciprocalTree := .branch r460 r461
private abbrev r463 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 102
private theorem rc463 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128832 r463 = true := by decide +kernel

private abbrev r464 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 103
private theorem rc464 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128896 r464 = true := by decide +kernel

private def r462 : MobiusReciprocalTree := .branch r463 r464
private def r458 : MobiusReciprocalTree := .branch r459 r462
private def r450 : MobiusReciprocalTree := .branch r451 r458
private abbrev r468 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 104
private theorem rc468 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128960 r468 = true := by decide +kernel

private abbrev r469 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 105
private theorem rc469 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129024 r469 = true := by decide +kernel

private def r467 : MobiusReciprocalTree := .branch r468 r469
private abbrev r471 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 106
private theorem rc471 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129088 r471 = true := by decide +kernel

private abbrev r472 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 107
private theorem rc472 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129152 r472 = true := by decide +kernel

private def r470 : MobiusReciprocalTree := .branch r471 r472
private def r466 : MobiusReciprocalTree := .branch r467 r470
private abbrev r475 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 108
private theorem rc475 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129216 r475 = true := by decide +kernel

private abbrev r476 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 109
private theorem rc476 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129280 r476 = true := by decide +kernel

private def r474 : MobiusReciprocalTree := .branch r475 r476
private abbrev r478 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 110
private theorem rc478 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129344 r478 = true := by decide +kernel

private abbrev r479 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 111
private theorem rc479 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129408 r479 = true := by decide +kernel

private def r477 : MobiusReciprocalTree := .branch r478 r479
private def r473 : MobiusReciprocalTree := .branch r474 r477
private def r465 : MobiusReciprocalTree := .branch r466 r473
private def r449 : MobiusReciprocalTree := .branch r450 r465
private abbrev r484 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 112
private theorem rc484 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129472 r484 = true := by decide +kernel

private abbrev r485 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 113
private theorem rc485 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129536 r485 = true := by decide +kernel

private def r483 : MobiusReciprocalTree := .branch r484 r485
private abbrev r487 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 114
private theorem rc487 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129600 r487 = true := by decide +kernel

private abbrev r488 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 115
private theorem rc488 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129664 r488 = true := by decide +kernel

private def r486 : MobiusReciprocalTree := .branch r487 r488
private def r482 : MobiusReciprocalTree := .branch r483 r486
private abbrev r491 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 116
private theorem rc491 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129728 r491 = true := by decide +kernel

private abbrev r492 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 117
private theorem rc492 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129792 r492 = true := by decide +kernel

private def r490 : MobiusReciprocalTree := .branch r491 r492
private abbrev r494 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 118
private theorem rc494 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129856 r494 = true := by decide +kernel

private abbrev r495 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 119
private theorem rc495 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129920 r495 = true := by decide +kernel

private def r493 : MobiusReciprocalTree := .branch r494 r495
private def r489 : MobiusReciprocalTree := .branch r490 r493
private def r481 : MobiusReciprocalTree := .branch r482 r489
private abbrev r499 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 120
private theorem rc499 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129984 r499 = true := by decide +kernel

private abbrev r500 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 121
private theorem rc500 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130048 r500 = true := by decide +kernel

private def r498 : MobiusReciprocalTree := .branch r499 r500
private abbrev r502 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 122
private theorem rc502 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130112 r502 = true := by decide +kernel

private abbrev r503 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 123
private theorem rc503 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130176 r503 = true := by decide +kernel

private def r501 : MobiusReciprocalTree := .branch r502 r503
private def r497 : MobiusReciprocalTree := .branch r498 r501
private abbrev r506 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 124
private theorem rc506 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130240 r506 = true := by decide +kernel

private abbrev r507 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 125
private theorem rc507 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130304 r507 = true := by decide +kernel

private def r505 : MobiusReciprocalTree := .branch r506 r507
private abbrev r509 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 126
private theorem rc509 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130368 r509 = true := by decide +kernel

private abbrev r510 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block137 127
private theorem rc510 : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130432 r510 = true := by decide +kernel

private def r508 : MobiusReciprocalTree := .branch r509 r510
private def r504 : MobiusReciprocalTree := .branch r505 r508
private def r496 : MobiusReciprocalTree := .branch r497 r504
private def r480 : MobiusReciprocalTree := .branch r481 r496
private def r448 : MobiusReciprocalTree := .branch r449 r480
private def r384 : MobiusReciprocalTree := .branch r385 r448
private def r256 : MobiusReciprocalTree := .branch r257 r384
private def r0 : MobiusReciprocalTree := .branch r1 r256

theorem mobiusReciprocalPair068_checked_complete : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1114112 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block136 mobiusReciprocal1200001Block137) = true :=
  (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 8 1114112 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 7 1114112 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 1114112 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1114112 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1114112 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1114112 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1114112 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114112 _ _ (by decide) rc8 rc9 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114240 _ _ (by decide) rc11 rc12 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1114368 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114368 _ _ (by decide) rc15 rc16 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114496 _ _ (by decide) rc18 rc19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1114624 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1114624 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114624 _ _ (by decide) rc23 rc24 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114752 _ _ (by decide) rc26 rc27 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1114880 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1114880 _ _ (by decide) rc30 rc31 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115008 _ _ (by decide) rc33 rc34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1115136 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1115136 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1115136 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115136 _ _ (by decide) rc39 rc40 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115264 _ _ (by decide) rc42 rc43 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1115392 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115392 _ _ (by decide) rc46 rc47 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115520 _ _ (by decide) rc49 rc50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1115648 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1115648 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115648 _ _ (by decide) rc54 rc55 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115776 _ _ (by decide) rc57 rc58 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1115904 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1115904 _ _ (by decide) rc61 rc62 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116032 _ _ (by decide) rc64 rc65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1116160 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1116160 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1116160 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1116160 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116160 _ _ (by decide) rc71 rc72 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116288 _ _ (by decide) rc74 rc75 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1116416 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116416 _ _ (by decide) rc78 rc79 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116544 _ _ (by decide) rc81 rc82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1116672 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1116672 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116672 _ _ (by decide) rc86 rc87 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116800 _ _ (by decide) rc89 rc90 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1116928 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1116928 _ _ (by decide) rc93 rc94 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117056 _ _ (by decide) rc96 rc97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1117184 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1117184 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1117184 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117184 _ _ (by decide) rc102 rc103 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117312 _ _ (by decide) rc105 rc106 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1117440 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117440 _ _ (by decide) rc109 rc110 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117568 _ _ (by decide) rc112 rc113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1117696 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1117696 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117696 _ _ (by decide) rc117 rc118 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117824 _ _ (by decide) rc120 rc121 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1117952 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1117952 _ _ (by decide) rc124 rc125 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118080 _ _ (by decide) rc127 rc128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 1118208 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1118208 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1118208 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1118208 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1118208 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118208 _ _ (by decide) rc135 rc136 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118336 _ _ (by decide) rc138 rc139 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1118464 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118464 _ _ (by decide) rc142 rc143 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118592 _ _ (by decide) rc145 rc146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1118720 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1118720 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118720 _ _ (by decide) rc150 rc151 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118848 _ _ (by decide) rc153 rc154 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1118976 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1118976 _ _ (by decide) rc157 rc158 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119104 _ _ (by decide) rc160 rc161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1119232 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1119232 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1119232 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119232 _ _ (by decide) rc166 rc167 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119360 _ _ (by decide) rc169 rc170 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1119488 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119488 _ _ (by decide) rc173 rc174 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119616 _ _ (by decide) rc176 rc177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1119744 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1119744 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119744 _ _ (by decide) rc181 rc182 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1119872 _ _ (by decide) rc184 rc185 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1120000 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120000 _ _ (by decide) rc188 rc189 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120128 _ _ (by decide) rc191 rc192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1120256 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1120256 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1120256 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1120256 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120256 _ _ (by decide) rc198 rc199 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120384 _ _ (by decide) rc201 rc202 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1120512 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120512 _ _ (by decide) rc205 rc206 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120640 _ _ (by decide) rc208 rc209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1120768 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1120768 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120768 _ _ (by decide) rc213 rc214 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1120896 _ _ (by decide) rc216 rc217 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1121024 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121024 _ _ (by decide) rc220 rc221 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121152 _ _ (by decide) rc223 rc224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1121280 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1121280 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1121280 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121280 _ _ (by decide) rc229 rc230 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121408 _ _ (by decide) rc232 rc233 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1121536 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121536 _ _ (by decide) rc236 rc237 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121664 _ _ (by decide) rc239 rc240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1121792 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1121792 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121792 _ _ (by decide) rc244 rc245 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1121920 _ _ (by decide) rc247 rc248 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1122048 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122048 _ _ (by decide) rc251 rc252 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122176 _ _ (by decide) rc254 rc255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 7 1122304 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 1122304 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1122304 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1122304 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1122304 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1122304 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122304 _ _ (by decide) rc263 rc264 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122432 _ _ (by decide) rc266 rc267 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1122560 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122560 _ _ (by decide) rc270 rc271 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122688 _ _ (by decide) rc273 rc274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1122816 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1122816 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122816 _ _ (by decide) rc278 rc279 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1122944 _ _ (by decide) rc281 rc282 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1123072 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123072 _ _ (by decide) rc285 rc286 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123200 _ _ (by decide) rc288 rc289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1123328 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1123328 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1123328 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123328 _ _ (by decide) rc294 rc295 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123456 _ _ (by decide) rc297 rc298 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1123584 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123584 _ _ (by decide) rc301 rc302 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123712 _ _ (by decide) rc304 rc305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1123840 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1123840 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123840 _ _ (by decide) rc309 rc310 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1123968 _ _ (by decide) rc312 rc313 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1124096 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124096 _ _ (by decide) rc316 rc317 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124224 _ _ (by decide) rc319 rc320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1124352 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1124352 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1124352 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1124352 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124352 _ _ (by decide) rc326 rc327 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124480 _ _ (by decide) rc329 rc330 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1124608 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124608 _ _ (by decide) rc333 rc334 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124736 _ _ (by decide) rc336 rc337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1124864 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1124864 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124864 _ _ (by decide) rc341 rc342 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1124992 _ _ (by decide) rc344 rc345 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1125120 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125120 _ _ (by decide) rc348 rc349 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125248 _ _ (by decide) rc351 rc352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1125376 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1125376 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1125376 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125376 _ _ (by decide) rc357 rc358 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125504 _ _ (by decide) rc360 rc361 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1125632 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125632 _ _ (by decide) rc364 rc365 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125760 _ _ (by decide) rc367 rc368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1125888 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1125888 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1125888 _ _ (by decide) rc372 rc373 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126016 _ _ (by decide) rc375 rc376 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1126144 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126144 _ _ (by decide) rc379 rc380 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126272 _ _ (by decide) rc382 rc383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 6 1126400 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1126400 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1126400 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1126400 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1126400 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126400 _ _ (by decide) rc390 rc391 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126528 _ _ (by decide) rc393 rc394 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1126656 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126656 _ _ (by decide) rc397 rc398 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126784 _ _ (by decide) rc400 rc401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1126912 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1126912 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1126912 _ _ (by decide) rc405 rc406 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127040 _ _ (by decide) rc408 rc409 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1127168 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127168 _ _ (by decide) rc412 rc413 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127296 _ _ (by decide) rc415 rc416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1127424 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1127424 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1127424 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127424 _ _ (by decide) rc421 rc422 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127552 _ _ (by decide) rc424 rc425 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1127680 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127680 _ _ (by decide) rc428 rc429 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127808 _ _ (by decide) rc431 rc432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1127936 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1127936 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1127936 _ _ (by decide) rc436 rc437 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128064 _ _ (by decide) rc439 rc440 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1128192 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128192 _ _ (by decide) rc443 rc444 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128320 _ _ (by decide) rc446 rc447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 5 1128448 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1128448 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1128448 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1128448 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128448 _ _ (by decide) rc453 rc454 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128576 _ _ (by decide) rc456 rc457 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1128704 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128704 _ _ (by decide) rc460 rc461 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128832 _ _ (by decide) rc463 rc464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1128960 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1128960 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1128960 _ _ (by decide) rc468 rc469 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129088 _ _ (by decide) rc471 rc472 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1129216 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129216 _ _ (by decide) rc475 rc476 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129344 _ _ (by decide) rc478 rc479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 4 1129472 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1129472 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1129472 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129472 _ _ (by decide) rc484 rc485 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129600 _ _ (by decide) rc487 rc488 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1129728 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129728 _ _ (by decide) rc491 rc492 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129856 _ _ (by decide) rc494 rc495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 3 1129984 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1129984 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1129984 _ _ (by decide) rc499 rc500 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130112 _ _ (by decide) rc502 rc503 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 2 1130240 _ _ (by decide) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130240 _ _ (by decide) rc506 rc507 (by decide +kernel)) (mobiusReciprocalTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 1 1130368 _ _ (by decide) rc509 rc510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott
end

open Helfgott
theorem solution : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1114112 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block136 mobiusReciprocal1200001Block137) = true := Helfgott.mobiusReciprocalPair068_checked_complete
#print axioms solution
