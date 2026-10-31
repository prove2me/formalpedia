-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Mid.Tab.gtrue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:59:38.657991+00:00
-- url     : https://prove2.me/submissions/7e17a577-de37-4464-9611-c4eedfeeb682

import Mathlib
import Definitions.Def_OAIQ026G002
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_0_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_10_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_11_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_12_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_13_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_14_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_15_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_16_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_17_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_18_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_19_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_1_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_20_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_21_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_22_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_23_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_24_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_25_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_26_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_2_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_3_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_4_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_5_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_6_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_7_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_8_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_ctrue_9_0_90

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Data
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Tag CJet Jet Profile Cert Cert.IV

lemma byRun (p:ℕ→Bool) (n m k:ℕ) (he:n+m=k) (h:runB p n m=true): By p n k := by
  subst k
  induction m with
  | zero=> intro i h1 h2; omega
  | succ m ih=>
    simp only [runB,Bool.and_eq_true] at h
    intro i h1 h2; by_cases H:i=n+m
    · exact H.symm ▸ h.1
    apply ih h.2 _ h1; omega
lemma byJoin {p:ℕ→Bool} {x y z:ℕ} (h:By p x y) (hh:By p y z):
    By p x z := by intro i he hz; rcases lt_or_ge i y with h'|h'; exact h i he h'; exact hh i h' hz
end GeneralMahler.SCal.Grid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue27
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_27_0_2 : By (tile Cn true 27) 0 2 := by
  apply byRun (tile Cn true 27) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_27_2_5 : By (tile Cn true 27) 2 5 := by
  apply byRun (tile Cn true 27) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_27_0_5 : By (tile Cn true 27) 0 5 := byJoin ctrue_27_0_2 ctrue_27_2_5
lemma ctrue_27_5_8 : By (tile Cn true 27) 5 8 := by
  apply byRun (tile Cn true 27) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_27_8_11 : By (tile Cn true 27) 8 11 := by
  apply byRun (tile Cn true 27) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_27_5_11 : By (tile Cn true 27) 5 11 := byJoin ctrue_27_5_8 ctrue_27_8_11
lemma ctrue_27_0_11 : By (tile Cn true 27) 0 11 := byJoin ctrue_27_0_5 ctrue_27_5_11
lemma ctrue_27_11_13 : By (tile Cn true 27) 11 13 := by
  apply byRun (tile Cn true 27) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_27_13_16 : By (tile Cn true 27) 13 16 := by
  apply byRun (tile Cn true 27) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_27_11_16 : By (tile Cn true 27) 11 16 := byJoin ctrue_27_11_13 ctrue_27_13_16
lemma ctrue_27_16_19 : By (tile Cn true 27) 16 19 := by
  apply byRun (tile Cn true 27) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_27_19_22 : By (tile Cn true 27) 19 22 := by
  apply byRun (tile Cn true 27) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_27_16_22 : By (tile Cn true 27) 16 22 := byJoin ctrue_27_16_19 ctrue_27_19_22
lemma ctrue_27_11_22 : By (tile Cn true 27) 11 22 := byJoin ctrue_27_11_16 ctrue_27_16_22
lemma ctrue_27_0_22 : By (tile Cn true 27) 0 22 := byJoin ctrue_27_0_11 ctrue_27_11_22
lemma ctrue_27_22_24 : By (tile Cn true 27) 22 24 := by
  apply byRun (tile Cn true 27) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_27_24_27 : By (tile Cn true 27) 24 27 := by
  apply byRun (tile Cn true 27) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_27_22_27 : By (tile Cn true 27) 22 27 := byJoin ctrue_27_22_24 ctrue_27_24_27
lemma ctrue_27_27_30 : By (tile Cn true 27) 27 30 := by
  apply byRun (tile Cn true 27) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_27_30_33 : By (tile Cn true 27) 30 33 := by
  apply byRun (tile Cn true 27) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_27_27_33 : By (tile Cn true 27) 27 33 := byJoin ctrue_27_27_30 ctrue_27_30_33
lemma ctrue_27_22_33 : By (tile Cn true 27) 22 33 := byJoin ctrue_27_22_27 ctrue_27_27_33
lemma ctrue_27_33_36 : By (tile Cn true 27) 33 36 := by
  apply byRun (tile Cn true 27) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_27_36_39 : By (tile Cn true 27) 36 39 := by
  apply byRun (tile Cn true 27) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_27_33_39 : By (tile Cn true 27) 33 39 := byJoin ctrue_27_33_36 ctrue_27_36_39
lemma ctrue_27_39_42 : By (tile Cn true 27) 39 42 := by
  apply byRun (tile Cn true 27) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_27_42_45 : By (tile Cn true 27) 42 45 := by
  apply byRun (tile Cn true 27) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_27_39_45 : By (tile Cn true 27) 39 45 := byJoin ctrue_27_39_42 ctrue_27_42_45
lemma ctrue_27_33_45 : By (tile Cn true 27) 33 45 := byJoin ctrue_27_33_39 ctrue_27_39_45
lemma ctrue_27_22_45 : By (tile Cn true 27) 22 45 := byJoin ctrue_27_22_33 ctrue_27_33_45
lemma ctrue_27_0_45 : By (tile Cn true 27) 0 45 := byJoin ctrue_27_0_22 ctrue_27_22_45
lemma ctrue_27_45_47 : By (tile Cn true 27) 45 47 := by
  apply byRun (tile Cn true 27) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_27_47_50 : By (tile Cn true 27) 47 50 := by
  apply byRun (tile Cn true 27) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_27_45_50 : By (tile Cn true 27) 45 50 := byJoin ctrue_27_45_47 ctrue_27_47_50
lemma ctrue_27_50_53 : By (tile Cn true 27) 50 53 := by
  apply byRun (tile Cn true 27) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_27_53_56 : By (tile Cn true 27) 53 56 := by
  apply byRun (tile Cn true 27) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_27_50_56 : By (tile Cn true 27) 50 56 := byJoin ctrue_27_50_53 ctrue_27_53_56
lemma ctrue_27_45_56 : By (tile Cn true 27) 45 56 := byJoin ctrue_27_45_50 ctrue_27_50_56
lemma ctrue_27_56_58 : By (tile Cn true 27) 56 58 := by
  apply byRun (tile Cn true 27) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_27_58_61 : By (tile Cn true 27) 58 61 := by
  apply byRun (tile Cn true 27) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_27_56_61 : By (tile Cn true 27) 56 61 := byJoin ctrue_27_56_58 ctrue_27_58_61
lemma ctrue_27_61_64 : By (tile Cn true 27) 61 64 := by
  apply byRun (tile Cn true 27) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_27_64_67 : By (tile Cn true 27) 64 67 := by
  apply byRun (tile Cn true 27) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_27_61_67 : By (tile Cn true 27) 61 67 := byJoin ctrue_27_61_64 ctrue_27_64_67
lemma ctrue_27_56_67 : By (tile Cn true 27) 56 67 := byJoin ctrue_27_56_61 ctrue_27_61_67
lemma ctrue_27_45_67 : By (tile Cn true 27) 45 67 := byJoin ctrue_27_45_56 ctrue_27_56_67
lemma ctrue_27_67_69 : By (tile Cn true 27) 67 69 := by
  apply byRun (tile Cn true 27) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_27_69_72 : By (tile Cn true 27) 69 72 := by
  apply byRun (tile Cn true 27) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_27_67_72 : By (tile Cn true 27) 67 72 := byJoin ctrue_27_67_69 ctrue_27_69_72
lemma ctrue_27_72_75 : By (tile Cn true 27) 72 75 := by
  apply byRun (tile Cn true 27) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_27_75_78 : By (tile Cn true 27) 75 78 := by
  apply byRun (tile Cn true 27) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_27_72_78 : By (tile Cn true 27) 72 78 := byJoin ctrue_27_72_75 ctrue_27_75_78
lemma ctrue_27_67_78 : By (tile Cn true 27) 67 78 := byJoin ctrue_27_67_72 ctrue_27_72_78
lemma ctrue_27_78_81 : By (tile Cn true 27) 78 81 := by
  apply byRun (tile Cn true 27) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_27_81_84 : By (tile Cn true 27) 81 84 := by
  apply byRun (tile Cn true 27) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_27_78_84 : By (tile Cn true 27) 78 84 := byJoin ctrue_27_78_81 ctrue_27_81_84
lemma ctrue_27_84_87 : By (tile Cn true 27) 84 87 := by
  apply byRun (tile Cn true 27) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_27_87_90 : By (tile Cn true 27) 87 90 := by
  apply byRun (tile Cn true 27) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_27_84_90 : By (tile Cn true 27) 84 90 := byJoin ctrue_27_84_87 ctrue_27_87_90
lemma ctrue_27_78_90 : By (tile Cn true 27) 78 90 := byJoin ctrue_27_78_84 ctrue_27_84_90
lemma ctrue_27_67_90 : By (tile Cn true 27) 67 90 := byJoin ctrue_27_67_78 ctrue_27_78_90
lemma ctrue_27_45_90 : By (tile Cn true 27) 45 90 := byJoin ctrue_27_45_67 ctrue_27_67_90
lemma ctrue_27_0_90 : By (tile Cn true 27) 0 90 := byJoin ctrue_27_0_45 ctrue_27_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue28
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_28_0_2 : By (tile Cn true 28) 0 2 := by
  apply byRun (tile Cn true 28) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_28_2_5 : By (tile Cn true 28) 2 5 := by
  apply byRun (tile Cn true 28) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_28_0_5 : By (tile Cn true 28) 0 5 := byJoin ctrue_28_0_2 ctrue_28_2_5
lemma ctrue_28_5_8 : By (tile Cn true 28) 5 8 := by
  apply byRun (tile Cn true 28) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_28_8_11 : By (tile Cn true 28) 8 11 := by
  apply byRun (tile Cn true 28) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_28_5_11 : By (tile Cn true 28) 5 11 := byJoin ctrue_28_5_8 ctrue_28_8_11
lemma ctrue_28_0_11 : By (tile Cn true 28) 0 11 := byJoin ctrue_28_0_5 ctrue_28_5_11
lemma ctrue_28_11_13 : By (tile Cn true 28) 11 13 := by
  apply byRun (tile Cn true 28) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_28_13_16 : By (tile Cn true 28) 13 16 := by
  apply byRun (tile Cn true 28) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_28_11_16 : By (tile Cn true 28) 11 16 := byJoin ctrue_28_11_13 ctrue_28_13_16
lemma ctrue_28_16_19 : By (tile Cn true 28) 16 19 := by
  apply byRun (tile Cn true 28) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_28_19_22 : By (tile Cn true 28) 19 22 := by
  apply byRun (tile Cn true 28) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_28_16_22 : By (tile Cn true 28) 16 22 := byJoin ctrue_28_16_19 ctrue_28_19_22
lemma ctrue_28_11_22 : By (tile Cn true 28) 11 22 := byJoin ctrue_28_11_16 ctrue_28_16_22
lemma ctrue_28_0_22 : By (tile Cn true 28) 0 22 := byJoin ctrue_28_0_11 ctrue_28_11_22
lemma ctrue_28_22_24 : By (tile Cn true 28) 22 24 := by
  apply byRun (tile Cn true 28) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_28_24_27 : By (tile Cn true 28) 24 27 := by
  apply byRun (tile Cn true 28) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_28_22_27 : By (tile Cn true 28) 22 27 := byJoin ctrue_28_22_24 ctrue_28_24_27
lemma ctrue_28_27_30 : By (tile Cn true 28) 27 30 := by
  apply byRun (tile Cn true 28) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_28_30_33 : By (tile Cn true 28) 30 33 := by
  apply byRun (tile Cn true 28) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_28_27_33 : By (tile Cn true 28) 27 33 := byJoin ctrue_28_27_30 ctrue_28_30_33
lemma ctrue_28_22_33 : By (tile Cn true 28) 22 33 := byJoin ctrue_28_22_27 ctrue_28_27_33
lemma ctrue_28_33_36 : By (tile Cn true 28) 33 36 := by
  apply byRun (tile Cn true 28) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_28_36_39 : By (tile Cn true 28) 36 39 := by
  apply byRun (tile Cn true 28) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_28_33_39 : By (tile Cn true 28) 33 39 := byJoin ctrue_28_33_36 ctrue_28_36_39
lemma ctrue_28_39_42 : By (tile Cn true 28) 39 42 := by
  apply byRun (tile Cn true 28) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_28_42_45 : By (tile Cn true 28) 42 45 := by
  apply byRun (tile Cn true 28) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_28_39_45 : By (tile Cn true 28) 39 45 := byJoin ctrue_28_39_42 ctrue_28_42_45
lemma ctrue_28_33_45 : By (tile Cn true 28) 33 45 := byJoin ctrue_28_33_39 ctrue_28_39_45
lemma ctrue_28_22_45 : By (tile Cn true 28) 22 45 := byJoin ctrue_28_22_33 ctrue_28_33_45
lemma ctrue_28_0_45 : By (tile Cn true 28) 0 45 := byJoin ctrue_28_0_22 ctrue_28_22_45
lemma ctrue_28_45_47 : By (tile Cn true 28) 45 47 := by
  apply byRun (tile Cn true 28) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_28_47_50 : By (tile Cn true 28) 47 50 := by
  apply byRun (tile Cn true 28) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_28_45_50 : By (tile Cn true 28) 45 50 := byJoin ctrue_28_45_47 ctrue_28_47_50
lemma ctrue_28_50_53 : By (tile Cn true 28) 50 53 := by
  apply byRun (tile Cn true 28) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_28_53_56 : By (tile Cn true 28) 53 56 := by
  apply byRun (tile Cn true 28) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_28_50_56 : By (tile Cn true 28) 50 56 := byJoin ctrue_28_50_53 ctrue_28_53_56
lemma ctrue_28_45_56 : By (tile Cn true 28) 45 56 := byJoin ctrue_28_45_50 ctrue_28_50_56
lemma ctrue_28_56_58 : By (tile Cn true 28) 56 58 := by
  apply byRun (tile Cn true 28) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_28_58_61 : By (tile Cn true 28) 58 61 := by
  apply byRun (tile Cn true 28) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_28_56_61 : By (tile Cn true 28) 56 61 := byJoin ctrue_28_56_58 ctrue_28_58_61
lemma ctrue_28_61_64 : By (tile Cn true 28) 61 64 := by
  apply byRun (tile Cn true 28) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_28_64_67 : By (tile Cn true 28) 64 67 := by
  apply byRun (tile Cn true 28) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_28_61_67 : By (tile Cn true 28) 61 67 := byJoin ctrue_28_61_64 ctrue_28_64_67
lemma ctrue_28_56_67 : By (tile Cn true 28) 56 67 := byJoin ctrue_28_56_61 ctrue_28_61_67
lemma ctrue_28_45_67 : By (tile Cn true 28) 45 67 := byJoin ctrue_28_45_56 ctrue_28_56_67
lemma ctrue_28_67_69 : By (tile Cn true 28) 67 69 := by
  apply byRun (tile Cn true 28) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_28_69_72 : By (tile Cn true 28) 69 72 := by
  apply byRun (tile Cn true 28) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_28_67_72 : By (tile Cn true 28) 67 72 := byJoin ctrue_28_67_69 ctrue_28_69_72
lemma ctrue_28_72_75 : By (tile Cn true 28) 72 75 := by
  apply byRun (tile Cn true 28) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_28_75_78 : By (tile Cn true 28) 75 78 := by
  apply byRun (tile Cn true 28) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_28_72_78 : By (tile Cn true 28) 72 78 := byJoin ctrue_28_72_75 ctrue_28_75_78
lemma ctrue_28_67_78 : By (tile Cn true 28) 67 78 := byJoin ctrue_28_67_72 ctrue_28_72_78
lemma ctrue_28_78_81 : By (tile Cn true 28) 78 81 := by
  apply byRun (tile Cn true 28) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_28_81_84 : By (tile Cn true 28) 81 84 := by
  apply byRun (tile Cn true 28) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_28_78_84 : By (tile Cn true 28) 78 84 := byJoin ctrue_28_78_81 ctrue_28_81_84
lemma ctrue_28_84_87 : By (tile Cn true 28) 84 87 := by
  apply byRun (tile Cn true 28) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_28_87_90 : By (tile Cn true 28) 87 90 := by
  apply byRun (tile Cn true 28) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_28_84_90 : By (tile Cn true 28) 84 90 := byJoin ctrue_28_84_87 ctrue_28_87_90
lemma ctrue_28_78_90 : By (tile Cn true 28) 78 90 := byJoin ctrue_28_78_84 ctrue_28_84_90
lemma ctrue_28_67_90 : By (tile Cn true 28) 67 90 := byJoin ctrue_28_67_78 ctrue_28_78_90
lemma ctrue_28_45_90 : By (tile Cn true 28) 45 90 := byJoin ctrue_28_45_67 ctrue_28_67_90
lemma ctrue_28_0_90 : By (tile Cn true 28) 0 90 := byJoin ctrue_28_0_45 ctrue_28_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue29
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_29_0_2 : By (tile Cn true 29) 0 2 := by
  apply byRun (tile Cn true 29) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_29_2_5 : By (tile Cn true 29) 2 5 := by
  apply byRun (tile Cn true 29) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_29_0_5 : By (tile Cn true 29) 0 5 := byJoin ctrue_29_0_2 ctrue_29_2_5
lemma ctrue_29_5_8 : By (tile Cn true 29) 5 8 := by
  apply byRun (tile Cn true 29) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_29_8_11 : By (tile Cn true 29) 8 11 := by
  apply byRun (tile Cn true 29) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_29_5_11 : By (tile Cn true 29) 5 11 := byJoin ctrue_29_5_8 ctrue_29_8_11
lemma ctrue_29_0_11 : By (tile Cn true 29) 0 11 := byJoin ctrue_29_0_5 ctrue_29_5_11
lemma ctrue_29_11_13 : By (tile Cn true 29) 11 13 := by
  apply byRun (tile Cn true 29) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_29_13_16 : By (tile Cn true 29) 13 16 := by
  apply byRun (tile Cn true 29) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_29_11_16 : By (tile Cn true 29) 11 16 := byJoin ctrue_29_11_13 ctrue_29_13_16
lemma ctrue_29_16_19 : By (tile Cn true 29) 16 19 := by
  apply byRun (tile Cn true 29) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_29_19_22 : By (tile Cn true 29) 19 22 := by
  apply byRun (tile Cn true 29) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_29_16_22 : By (tile Cn true 29) 16 22 := byJoin ctrue_29_16_19 ctrue_29_19_22
lemma ctrue_29_11_22 : By (tile Cn true 29) 11 22 := byJoin ctrue_29_11_16 ctrue_29_16_22
lemma ctrue_29_0_22 : By (tile Cn true 29) 0 22 := byJoin ctrue_29_0_11 ctrue_29_11_22
lemma ctrue_29_22_24 : By (tile Cn true 29) 22 24 := by
  apply byRun (tile Cn true 29) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_29_24_27 : By (tile Cn true 29) 24 27 := by
  apply byRun (tile Cn true 29) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_29_22_27 : By (tile Cn true 29) 22 27 := byJoin ctrue_29_22_24 ctrue_29_24_27
lemma ctrue_29_27_30 : By (tile Cn true 29) 27 30 := by
  apply byRun (tile Cn true 29) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_29_30_33 : By (tile Cn true 29) 30 33 := by
  apply byRun (tile Cn true 29) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_29_27_33 : By (tile Cn true 29) 27 33 := byJoin ctrue_29_27_30 ctrue_29_30_33
lemma ctrue_29_22_33 : By (tile Cn true 29) 22 33 := byJoin ctrue_29_22_27 ctrue_29_27_33
lemma ctrue_29_33_36 : By (tile Cn true 29) 33 36 := by
  apply byRun (tile Cn true 29) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_29_36_39 : By (tile Cn true 29) 36 39 := by
  apply byRun (tile Cn true 29) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_29_33_39 : By (tile Cn true 29) 33 39 := byJoin ctrue_29_33_36 ctrue_29_36_39
lemma ctrue_29_39_42 : By (tile Cn true 29) 39 42 := by
  apply byRun (tile Cn true 29) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_29_42_45 : By (tile Cn true 29) 42 45 := by
  apply byRun (tile Cn true 29) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_29_39_45 : By (tile Cn true 29) 39 45 := byJoin ctrue_29_39_42 ctrue_29_42_45
lemma ctrue_29_33_45 : By (tile Cn true 29) 33 45 := byJoin ctrue_29_33_39 ctrue_29_39_45
lemma ctrue_29_22_45 : By (tile Cn true 29) 22 45 := byJoin ctrue_29_22_33 ctrue_29_33_45
lemma ctrue_29_0_45 : By (tile Cn true 29) 0 45 := byJoin ctrue_29_0_22 ctrue_29_22_45
lemma ctrue_29_45_47 : By (tile Cn true 29) 45 47 := by
  apply byRun (tile Cn true 29) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_29_47_50 : By (tile Cn true 29) 47 50 := by
  apply byRun (tile Cn true 29) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_29_45_50 : By (tile Cn true 29) 45 50 := byJoin ctrue_29_45_47 ctrue_29_47_50
lemma ctrue_29_50_53 : By (tile Cn true 29) 50 53 := by
  apply byRun (tile Cn true 29) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_29_53_56 : By (tile Cn true 29) 53 56 := by
  apply byRun (tile Cn true 29) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_29_50_56 : By (tile Cn true 29) 50 56 := byJoin ctrue_29_50_53 ctrue_29_53_56
lemma ctrue_29_45_56 : By (tile Cn true 29) 45 56 := byJoin ctrue_29_45_50 ctrue_29_50_56
lemma ctrue_29_56_58 : By (tile Cn true 29) 56 58 := by
  apply byRun (tile Cn true 29) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_29_58_61 : By (tile Cn true 29) 58 61 := by
  apply byRun (tile Cn true 29) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_29_56_61 : By (tile Cn true 29) 56 61 := byJoin ctrue_29_56_58 ctrue_29_58_61
lemma ctrue_29_61_64 : By (tile Cn true 29) 61 64 := by
  apply byRun (tile Cn true 29) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_29_64_67 : By (tile Cn true 29) 64 67 := by
  apply byRun (tile Cn true 29) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_29_61_67 : By (tile Cn true 29) 61 67 := byJoin ctrue_29_61_64 ctrue_29_64_67
lemma ctrue_29_56_67 : By (tile Cn true 29) 56 67 := byJoin ctrue_29_56_61 ctrue_29_61_67
lemma ctrue_29_45_67 : By (tile Cn true 29) 45 67 := byJoin ctrue_29_45_56 ctrue_29_56_67
lemma ctrue_29_67_69 : By (tile Cn true 29) 67 69 := by
  apply byRun (tile Cn true 29) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_29_69_72 : By (tile Cn true 29) 69 72 := by
  apply byRun (tile Cn true 29) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_29_67_72 : By (tile Cn true 29) 67 72 := byJoin ctrue_29_67_69 ctrue_29_69_72
lemma ctrue_29_72_75 : By (tile Cn true 29) 72 75 := by
  apply byRun (tile Cn true 29) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_29_75_78 : By (tile Cn true 29) 75 78 := by
  apply byRun (tile Cn true 29) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_29_72_78 : By (tile Cn true 29) 72 78 := byJoin ctrue_29_72_75 ctrue_29_75_78
lemma ctrue_29_67_78 : By (tile Cn true 29) 67 78 := byJoin ctrue_29_67_72 ctrue_29_72_78
lemma ctrue_29_78_81 : By (tile Cn true 29) 78 81 := by
  apply byRun (tile Cn true 29) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_29_81_84 : By (tile Cn true 29) 81 84 := by
  apply byRun (tile Cn true 29) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_29_78_84 : By (tile Cn true 29) 78 84 := byJoin ctrue_29_78_81 ctrue_29_81_84
lemma ctrue_29_84_87 : By (tile Cn true 29) 84 87 := by
  apply byRun (tile Cn true 29) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_29_87_90 : By (tile Cn true 29) 87 90 := by
  apply byRun (tile Cn true 29) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_29_84_90 : By (tile Cn true 29) 84 90 := byJoin ctrue_29_84_87 ctrue_29_87_90
lemma ctrue_29_78_90 : By (tile Cn true 29) 78 90 := byJoin ctrue_29_78_84 ctrue_29_84_90
lemma ctrue_29_67_90 : By (tile Cn true 29) 67 90 := byJoin ctrue_29_67_78 ctrue_29_78_90
lemma ctrue_29_45_90 : By (tile Cn true 29) 45 90 := byJoin ctrue_29_45_67 ctrue_29_67_90
lemma ctrue_29_0_90 : By (tile Cn true 29) 0 90 := byJoin ctrue_29_0_45 ctrue_29_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue30
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_30_0_2 : By (tile Cn true 30) 0 2 := by
  apply byRun (tile Cn true 30) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_30_2_5 : By (tile Cn true 30) 2 5 := by
  apply byRun (tile Cn true 30) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_30_0_5 : By (tile Cn true 30) 0 5 := byJoin ctrue_30_0_2 ctrue_30_2_5
lemma ctrue_30_5_8 : By (tile Cn true 30) 5 8 := by
  apply byRun (tile Cn true 30) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_30_8_11 : By (tile Cn true 30) 8 11 := by
  apply byRun (tile Cn true 30) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_30_5_11 : By (tile Cn true 30) 5 11 := byJoin ctrue_30_5_8 ctrue_30_8_11
lemma ctrue_30_0_11 : By (tile Cn true 30) 0 11 := byJoin ctrue_30_0_5 ctrue_30_5_11
lemma ctrue_30_11_13 : By (tile Cn true 30) 11 13 := by
  apply byRun (tile Cn true 30) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_30_13_16 : By (tile Cn true 30) 13 16 := by
  apply byRun (tile Cn true 30) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_30_11_16 : By (tile Cn true 30) 11 16 := byJoin ctrue_30_11_13 ctrue_30_13_16
lemma ctrue_30_16_19 : By (tile Cn true 30) 16 19 := by
  apply byRun (tile Cn true 30) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_30_19_22 : By (tile Cn true 30) 19 22 := by
  apply byRun (tile Cn true 30) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_30_16_22 : By (tile Cn true 30) 16 22 := byJoin ctrue_30_16_19 ctrue_30_19_22
lemma ctrue_30_11_22 : By (tile Cn true 30) 11 22 := byJoin ctrue_30_11_16 ctrue_30_16_22
lemma ctrue_30_0_22 : By (tile Cn true 30) 0 22 := byJoin ctrue_30_0_11 ctrue_30_11_22
lemma ctrue_30_22_24 : By (tile Cn true 30) 22 24 := by
  apply byRun (tile Cn true 30) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_30_24_27 : By (tile Cn true 30) 24 27 := by
  apply byRun (tile Cn true 30) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_30_22_27 : By (tile Cn true 30) 22 27 := byJoin ctrue_30_22_24 ctrue_30_24_27
lemma ctrue_30_27_30 : By (tile Cn true 30) 27 30 := by
  apply byRun (tile Cn true 30) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_30_30_33 : By (tile Cn true 30) 30 33 := by
  apply byRun (tile Cn true 30) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_30_27_33 : By (tile Cn true 30) 27 33 := byJoin ctrue_30_27_30 ctrue_30_30_33
lemma ctrue_30_22_33 : By (tile Cn true 30) 22 33 := byJoin ctrue_30_22_27 ctrue_30_27_33
lemma ctrue_30_33_36 : By (tile Cn true 30) 33 36 := by
  apply byRun (tile Cn true 30) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_30_36_39 : By (tile Cn true 30) 36 39 := by
  apply byRun (tile Cn true 30) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_30_33_39 : By (tile Cn true 30) 33 39 := byJoin ctrue_30_33_36 ctrue_30_36_39
lemma ctrue_30_39_42 : By (tile Cn true 30) 39 42 := by
  apply byRun (tile Cn true 30) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_30_42_45 : By (tile Cn true 30) 42 45 := by
  apply byRun (tile Cn true 30) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_30_39_45 : By (tile Cn true 30) 39 45 := byJoin ctrue_30_39_42 ctrue_30_42_45
lemma ctrue_30_33_45 : By (tile Cn true 30) 33 45 := byJoin ctrue_30_33_39 ctrue_30_39_45
lemma ctrue_30_22_45 : By (tile Cn true 30) 22 45 := byJoin ctrue_30_22_33 ctrue_30_33_45
lemma ctrue_30_0_45 : By (tile Cn true 30) 0 45 := byJoin ctrue_30_0_22 ctrue_30_22_45
lemma ctrue_30_45_47 : By (tile Cn true 30) 45 47 := by
  apply byRun (tile Cn true 30) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_30_47_50 : By (tile Cn true 30) 47 50 := by
  apply byRun (tile Cn true 30) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_30_45_50 : By (tile Cn true 30) 45 50 := byJoin ctrue_30_45_47 ctrue_30_47_50
lemma ctrue_30_50_53 : By (tile Cn true 30) 50 53 := by
  apply byRun (tile Cn true 30) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_30_53_56 : By (tile Cn true 30) 53 56 := by
  apply byRun (tile Cn true 30) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_30_50_56 : By (tile Cn true 30) 50 56 := byJoin ctrue_30_50_53 ctrue_30_53_56
lemma ctrue_30_45_56 : By (tile Cn true 30) 45 56 := byJoin ctrue_30_45_50 ctrue_30_50_56
lemma ctrue_30_56_58 : By (tile Cn true 30) 56 58 := by
  apply byRun (tile Cn true 30) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_30_58_61 : By (tile Cn true 30) 58 61 := by
  apply byRun (tile Cn true 30) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_30_56_61 : By (tile Cn true 30) 56 61 := byJoin ctrue_30_56_58 ctrue_30_58_61
lemma ctrue_30_61_64 : By (tile Cn true 30) 61 64 := by
  apply byRun (tile Cn true 30) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_30_64_67 : By (tile Cn true 30) 64 67 := by
  apply byRun (tile Cn true 30) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_30_61_67 : By (tile Cn true 30) 61 67 := byJoin ctrue_30_61_64 ctrue_30_64_67
lemma ctrue_30_56_67 : By (tile Cn true 30) 56 67 := byJoin ctrue_30_56_61 ctrue_30_61_67
lemma ctrue_30_45_67 : By (tile Cn true 30) 45 67 := byJoin ctrue_30_45_56 ctrue_30_56_67
lemma ctrue_30_67_69 : By (tile Cn true 30) 67 69 := by
  apply byRun (tile Cn true 30) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_30_69_72 : By (tile Cn true 30) 69 72 := by
  apply byRun (tile Cn true 30) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_30_67_72 : By (tile Cn true 30) 67 72 := byJoin ctrue_30_67_69 ctrue_30_69_72
lemma ctrue_30_72_75 : By (tile Cn true 30) 72 75 := by
  apply byRun (tile Cn true 30) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_30_75_78 : By (tile Cn true 30) 75 78 := by
  apply byRun (tile Cn true 30) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_30_72_78 : By (tile Cn true 30) 72 78 := byJoin ctrue_30_72_75 ctrue_30_75_78
lemma ctrue_30_67_78 : By (tile Cn true 30) 67 78 := byJoin ctrue_30_67_72 ctrue_30_72_78
lemma ctrue_30_78_81 : By (tile Cn true 30) 78 81 := by
  apply byRun (tile Cn true 30) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_30_81_84 : By (tile Cn true 30) 81 84 := by
  apply byRun (tile Cn true 30) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_30_78_84 : By (tile Cn true 30) 78 84 := byJoin ctrue_30_78_81 ctrue_30_81_84
lemma ctrue_30_84_87 : By (tile Cn true 30) 84 87 := by
  apply byRun (tile Cn true 30) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_30_87_90 : By (tile Cn true 30) 87 90 := by
  apply byRun (tile Cn true 30) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_30_84_90 : By (tile Cn true 30) 84 90 := byJoin ctrue_30_84_87 ctrue_30_87_90
lemma ctrue_30_78_90 : By (tile Cn true 30) 78 90 := byJoin ctrue_30_78_84 ctrue_30_84_90
lemma ctrue_30_67_90 : By (tile Cn true 30) 67 90 := byJoin ctrue_30_67_78 ctrue_30_78_90
lemma ctrue_30_45_90 : By (tile Cn true 30) 45 90 := byJoin ctrue_30_45_67 ctrue_30_67_90
lemma ctrue_30_0_90 : By (tile Cn true 30) 0 90 := byJoin ctrue_30_0_45 ctrue_30_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue31
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_31_0_2 : By (tile Cn true 31) 0 2 := by
  apply byRun (tile Cn true 31) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_31_2_5 : By (tile Cn true 31) 2 5 := by
  apply byRun (tile Cn true 31) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_31_0_5 : By (tile Cn true 31) 0 5 := byJoin ctrue_31_0_2 ctrue_31_2_5
lemma ctrue_31_5_8 : By (tile Cn true 31) 5 8 := by
  apply byRun (tile Cn true 31) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_31_8_11 : By (tile Cn true 31) 8 11 := by
  apply byRun (tile Cn true 31) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_31_5_11 : By (tile Cn true 31) 5 11 := byJoin ctrue_31_5_8 ctrue_31_8_11
lemma ctrue_31_0_11 : By (tile Cn true 31) 0 11 := byJoin ctrue_31_0_5 ctrue_31_5_11
lemma ctrue_31_11_13 : By (tile Cn true 31) 11 13 := by
  apply byRun (tile Cn true 31) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_31_13_16 : By (tile Cn true 31) 13 16 := by
  apply byRun (tile Cn true 31) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_31_11_16 : By (tile Cn true 31) 11 16 := byJoin ctrue_31_11_13 ctrue_31_13_16
lemma ctrue_31_16_19 : By (tile Cn true 31) 16 19 := by
  apply byRun (tile Cn true 31) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_31_19_22 : By (tile Cn true 31) 19 22 := by
  apply byRun (tile Cn true 31) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_31_16_22 : By (tile Cn true 31) 16 22 := byJoin ctrue_31_16_19 ctrue_31_19_22
lemma ctrue_31_11_22 : By (tile Cn true 31) 11 22 := byJoin ctrue_31_11_16 ctrue_31_16_22
lemma ctrue_31_0_22 : By (tile Cn true 31) 0 22 := byJoin ctrue_31_0_11 ctrue_31_11_22
lemma ctrue_31_22_24 : By (tile Cn true 31) 22 24 := by
  apply byRun (tile Cn true 31) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_31_24_27 : By (tile Cn true 31) 24 27 := by
  apply byRun (tile Cn true 31) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_31_22_27 : By (tile Cn true 31) 22 27 := byJoin ctrue_31_22_24 ctrue_31_24_27
lemma ctrue_31_27_30 : By (tile Cn true 31) 27 30 := by
  apply byRun (tile Cn true 31) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_31_30_33 : By (tile Cn true 31) 30 33 := by
  apply byRun (tile Cn true 31) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_31_27_33 : By (tile Cn true 31) 27 33 := byJoin ctrue_31_27_30 ctrue_31_30_33
lemma ctrue_31_22_33 : By (tile Cn true 31) 22 33 := byJoin ctrue_31_22_27 ctrue_31_27_33
lemma ctrue_31_33_36 : By (tile Cn true 31) 33 36 := by
  apply byRun (tile Cn true 31) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_31_36_39 : By (tile Cn true 31) 36 39 := by
  apply byRun (tile Cn true 31) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_31_33_39 : By (tile Cn true 31) 33 39 := byJoin ctrue_31_33_36 ctrue_31_36_39
lemma ctrue_31_39_42 : By (tile Cn true 31) 39 42 := by
  apply byRun (tile Cn true 31) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_31_42_45 : By (tile Cn true 31) 42 45 := by
  apply byRun (tile Cn true 31) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_31_39_45 : By (tile Cn true 31) 39 45 := byJoin ctrue_31_39_42 ctrue_31_42_45
lemma ctrue_31_33_45 : By (tile Cn true 31) 33 45 := byJoin ctrue_31_33_39 ctrue_31_39_45
lemma ctrue_31_22_45 : By (tile Cn true 31) 22 45 := byJoin ctrue_31_22_33 ctrue_31_33_45
lemma ctrue_31_0_45 : By (tile Cn true 31) 0 45 := byJoin ctrue_31_0_22 ctrue_31_22_45
lemma ctrue_31_45_47 : By (tile Cn true 31) 45 47 := by
  apply byRun (tile Cn true 31) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_31_47_50 : By (tile Cn true 31) 47 50 := by
  apply byRun (tile Cn true 31) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_31_45_50 : By (tile Cn true 31) 45 50 := byJoin ctrue_31_45_47 ctrue_31_47_50
lemma ctrue_31_50_53 : By (tile Cn true 31) 50 53 := by
  apply byRun (tile Cn true 31) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_31_53_56 : By (tile Cn true 31) 53 56 := by
  apply byRun (tile Cn true 31) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_31_50_56 : By (tile Cn true 31) 50 56 := byJoin ctrue_31_50_53 ctrue_31_53_56
lemma ctrue_31_45_56 : By (tile Cn true 31) 45 56 := byJoin ctrue_31_45_50 ctrue_31_50_56
lemma ctrue_31_56_58 : By (tile Cn true 31) 56 58 := by
  apply byRun (tile Cn true 31) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_31_58_61 : By (tile Cn true 31) 58 61 := by
  apply byRun (tile Cn true 31) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_31_56_61 : By (tile Cn true 31) 56 61 := byJoin ctrue_31_56_58 ctrue_31_58_61
lemma ctrue_31_61_64 : By (tile Cn true 31) 61 64 := by
  apply byRun (tile Cn true 31) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_31_64_67 : By (tile Cn true 31) 64 67 := by
  apply byRun (tile Cn true 31) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_31_61_67 : By (tile Cn true 31) 61 67 := byJoin ctrue_31_61_64 ctrue_31_64_67
lemma ctrue_31_56_67 : By (tile Cn true 31) 56 67 := byJoin ctrue_31_56_61 ctrue_31_61_67
lemma ctrue_31_45_67 : By (tile Cn true 31) 45 67 := byJoin ctrue_31_45_56 ctrue_31_56_67
lemma ctrue_31_67_69 : By (tile Cn true 31) 67 69 := by
  apply byRun (tile Cn true 31) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_31_69_72 : By (tile Cn true 31) 69 72 := by
  apply byRun (tile Cn true 31) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_31_67_72 : By (tile Cn true 31) 67 72 := byJoin ctrue_31_67_69 ctrue_31_69_72
lemma ctrue_31_72_75 : By (tile Cn true 31) 72 75 := by
  apply byRun (tile Cn true 31) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_31_75_78 : By (tile Cn true 31) 75 78 := by
  apply byRun (tile Cn true 31) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_31_72_78 : By (tile Cn true 31) 72 78 := byJoin ctrue_31_72_75 ctrue_31_75_78
lemma ctrue_31_67_78 : By (tile Cn true 31) 67 78 := byJoin ctrue_31_67_72 ctrue_31_72_78
lemma ctrue_31_78_81 : By (tile Cn true 31) 78 81 := by
  apply byRun (tile Cn true 31) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_31_81_84 : By (tile Cn true 31) 81 84 := by
  apply byRun (tile Cn true 31) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_31_78_84 : By (tile Cn true 31) 78 84 := byJoin ctrue_31_78_81 ctrue_31_81_84
lemma ctrue_31_84_87 : By (tile Cn true 31) 84 87 := by
  apply byRun (tile Cn true 31) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_31_87_90 : By (tile Cn true 31) 87 90 := by
  apply byRun (tile Cn true 31) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_31_84_90 : By (tile Cn true 31) 84 90 := byJoin ctrue_31_84_87 ctrue_31_87_90
lemma ctrue_31_78_90 : By (tile Cn true 31) 78 90 := byJoin ctrue_31_78_84 ctrue_31_84_90
lemma ctrue_31_67_90 : By (tile Cn true 31) 67 90 := byJoin ctrue_31_67_78 ctrue_31_78_90
lemma ctrue_31_45_90 : By (tile Cn true 31) 45 90 := byJoin ctrue_31_45_67 ctrue_31_67_90
lemma ctrue_31_0_90 : By (tile Cn true 31) 0 90 := byJoin ctrue_31_0_45 ctrue_31_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue32
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_32_0_2 : By (tile Cn true 32) 0 2 := by
  apply byRun (tile Cn true 32) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_32_2_5 : By (tile Cn true 32) 2 5 := by
  apply byRun (tile Cn true 32) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_32_0_5 : By (tile Cn true 32) 0 5 := byJoin ctrue_32_0_2 ctrue_32_2_5
lemma ctrue_32_5_8 : By (tile Cn true 32) 5 8 := by
  apply byRun (tile Cn true 32) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_32_8_11 : By (tile Cn true 32) 8 11 := by
  apply byRun (tile Cn true 32) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_32_5_11 : By (tile Cn true 32) 5 11 := byJoin ctrue_32_5_8 ctrue_32_8_11
lemma ctrue_32_0_11 : By (tile Cn true 32) 0 11 := byJoin ctrue_32_0_5 ctrue_32_5_11
lemma ctrue_32_11_13 : By (tile Cn true 32) 11 13 := by
  apply byRun (tile Cn true 32) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_32_13_16 : By (tile Cn true 32) 13 16 := by
  apply byRun (tile Cn true 32) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_32_11_16 : By (tile Cn true 32) 11 16 := byJoin ctrue_32_11_13 ctrue_32_13_16
lemma ctrue_32_16_19 : By (tile Cn true 32) 16 19 := by
  apply byRun (tile Cn true 32) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_32_19_22 : By (tile Cn true 32) 19 22 := by
  apply byRun (tile Cn true 32) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_32_16_22 : By (tile Cn true 32) 16 22 := byJoin ctrue_32_16_19 ctrue_32_19_22
lemma ctrue_32_11_22 : By (tile Cn true 32) 11 22 := byJoin ctrue_32_11_16 ctrue_32_16_22
lemma ctrue_32_0_22 : By (tile Cn true 32) 0 22 := byJoin ctrue_32_0_11 ctrue_32_11_22
lemma ctrue_32_22_24 : By (tile Cn true 32) 22 24 := by
  apply byRun (tile Cn true 32) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_32_24_27 : By (tile Cn true 32) 24 27 := by
  apply byRun (tile Cn true 32) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_32_22_27 : By (tile Cn true 32) 22 27 := byJoin ctrue_32_22_24 ctrue_32_24_27
lemma ctrue_32_27_30 : By (tile Cn true 32) 27 30 := by
  apply byRun (tile Cn true 32) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_32_30_33 : By (tile Cn true 32) 30 33 := by
  apply byRun (tile Cn true 32) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_32_27_33 : By (tile Cn true 32) 27 33 := byJoin ctrue_32_27_30 ctrue_32_30_33
lemma ctrue_32_22_33 : By (tile Cn true 32) 22 33 := byJoin ctrue_32_22_27 ctrue_32_27_33
lemma ctrue_32_33_36 : By (tile Cn true 32) 33 36 := by
  apply byRun (tile Cn true 32) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_32_36_39 : By (tile Cn true 32) 36 39 := by
  apply byRun (tile Cn true 32) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_32_33_39 : By (tile Cn true 32) 33 39 := byJoin ctrue_32_33_36 ctrue_32_36_39
lemma ctrue_32_39_42 : By (tile Cn true 32) 39 42 := by
  apply byRun (tile Cn true 32) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_32_42_45 : By (tile Cn true 32) 42 45 := by
  apply byRun (tile Cn true 32) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_32_39_45 : By (tile Cn true 32) 39 45 := byJoin ctrue_32_39_42 ctrue_32_42_45
lemma ctrue_32_33_45 : By (tile Cn true 32) 33 45 := byJoin ctrue_32_33_39 ctrue_32_39_45
lemma ctrue_32_22_45 : By (tile Cn true 32) 22 45 := byJoin ctrue_32_22_33 ctrue_32_33_45
lemma ctrue_32_0_45 : By (tile Cn true 32) 0 45 := byJoin ctrue_32_0_22 ctrue_32_22_45
lemma ctrue_32_45_47 : By (tile Cn true 32) 45 47 := by
  apply byRun (tile Cn true 32) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_32_47_50 : By (tile Cn true 32) 47 50 := by
  apply byRun (tile Cn true 32) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_32_45_50 : By (tile Cn true 32) 45 50 := byJoin ctrue_32_45_47 ctrue_32_47_50
lemma ctrue_32_50_53 : By (tile Cn true 32) 50 53 := by
  apply byRun (tile Cn true 32) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_32_53_56 : By (tile Cn true 32) 53 56 := by
  apply byRun (tile Cn true 32) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_32_50_56 : By (tile Cn true 32) 50 56 := byJoin ctrue_32_50_53 ctrue_32_53_56
lemma ctrue_32_45_56 : By (tile Cn true 32) 45 56 := byJoin ctrue_32_45_50 ctrue_32_50_56
lemma ctrue_32_56_58 : By (tile Cn true 32) 56 58 := by
  apply byRun (tile Cn true 32) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_32_58_61 : By (tile Cn true 32) 58 61 := by
  apply byRun (tile Cn true 32) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_32_56_61 : By (tile Cn true 32) 56 61 := byJoin ctrue_32_56_58 ctrue_32_58_61
lemma ctrue_32_61_64 : By (tile Cn true 32) 61 64 := by
  apply byRun (tile Cn true 32) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_32_64_67 : By (tile Cn true 32) 64 67 := by
  apply byRun (tile Cn true 32) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_32_61_67 : By (tile Cn true 32) 61 67 := byJoin ctrue_32_61_64 ctrue_32_64_67
lemma ctrue_32_56_67 : By (tile Cn true 32) 56 67 := byJoin ctrue_32_56_61 ctrue_32_61_67
lemma ctrue_32_45_67 : By (tile Cn true 32) 45 67 := byJoin ctrue_32_45_56 ctrue_32_56_67
lemma ctrue_32_67_69 : By (tile Cn true 32) 67 69 := by
  apply byRun (tile Cn true 32) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_32_69_72 : By (tile Cn true 32) 69 72 := by
  apply byRun (tile Cn true 32) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_32_67_72 : By (tile Cn true 32) 67 72 := byJoin ctrue_32_67_69 ctrue_32_69_72
lemma ctrue_32_72_75 : By (tile Cn true 32) 72 75 := by
  apply byRun (tile Cn true 32) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_32_75_78 : By (tile Cn true 32) 75 78 := by
  apply byRun (tile Cn true 32) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_32_72_78 : By (tile Cn true 32) 72 78 := byJoin ctrue_32_72_75 ctrue_32_75_78
lemma ctrue_32_67_78 : By (tile Cn true 32) 67 78 := byJoin ctrue_32_67_72 ctrue_32_72_78
lemma ctrue_32_78_81 : By (tile Cn true 32) 78 81 := by
  apply byRun (tile Cn true 32) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_32_81_84 : By (tile Cn true 32) 81 84 := by
  apply byRun (tile Cn true 32) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_32_78_84 : By (tile Cn true 32) 78 84 := byJoin ctrue_32_78_81 ctrue_32_81_84
lemma ctrue_32_84_87 : By (tile Cn true 32) 84 87 := by
  apply byRun (tile Cn true 32) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_32_87_90 : By (tile Cn true 32) 87 90 := by
  apply byRun (tile Cn true 32) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_32_84_90 : By (tile Cn true 32) 84 90 := byJoin ctrue_32_84_87 ctrue_32_87_90
lemma ctrue_32_78_90 : By (tile Cn true 32) 78 90 := byJoin ctrue_32_78_84 ctrue_32_84_90
lemma ctrue_32_67_90 : By (tile Cn true 32) 67 90 := byJoin ctrue_32_67_78 ctrue_32_78_90
lemma ctrue_32_45_90 : By (tile Cn true 32) 45 90 := byJoin ctrue_32_45_67 ctrue_32_67_90
lemma ctrue_32_0_90 : By (tile Cn true 32) 0 90 := byJoin ctrue_32_0_45 ctrue_32_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue33
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_33_0_2 : By (tile Cn true 33) 0 2 := by
  apply byRun (tile Cn true 33) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_33_2_5 : By (tile Cn true 33) 2 5 := by
  apply byRun (tile Cn true 33) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_33_0_5 : By (tile Cn true 33) 0 5 := byJoin ctrue_33_0_2 ctrue_33_2_5
lemma ctrue_33_5_8 : By (tile Cn true 33) 5 8 := by
  apply byRun (tile Cn true 33) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_33_8_11 : By (tile Cn true 33) 8 11 := by
  apply byRun (tile Cn true 33) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_33_5_11 : By (tile Cn true 33) 5 11 := byJoin ctrue_33_5_8 ctrue_33_8_11
lemma ctrue_33_0_11 : By (tile Cn true 33) 0 11 := byJoin ctrue_33_0_5 ctrue_33_5_11
lemma ctrue_33_11_13 : By (tile Cn true 33) 11 13 := by
  apply byRun (tile Cn true 33) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_33_13_16 : By (tile Cn true 33) 13 16 := by
  apply byRun (tile Cn true 33) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_33_11_16 : By (tile Cn true 33) 11 16 := byJoin ctrue_33_11_13 ctrue_33_13_16
lemma ctrue_33_16_19 : By (tile Cn true 33) 16 19 := by
  apply byRun (tile Cn true 33) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_33_19_22 : By (tile Cn true 33) 19 22 := by
  apply byRun (tile Cn true 33) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_33_16_22 : By (tile Cn true 33) 16 22 := byJoin ctrue_33_16_19 ctrue_33_19_22
lemma ctrue_33_11_22 : By (tile Cn true 33) 11 22 := byJoin ctrue_33_11_16 ctrue_33_16_22
lemma ctrue_33_0_22 : By (tile Cn true 33) 0 22 := byJoin ctrue_33_0_11 ctrue_33_11_22
lemma ctrue_33_22_24 : By (tile Cn true 33) 22 24 := by
  apply byRun (tile Cn true 33) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_33_24_27 : By (tile Cn true 33) 24 27 := by
  apply byRun (tile Cn true 33) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_33_22_27 : By (tile Cn true 33) 22 27 := byJoin ctrue_33_22_24 ctrue_33_24_27
lemma ctrue_33_27_30 : By (tile Cn true 33) 27 30 := by
  apply byRun (tile Cn true 33) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_33_30_33 : By (tile Cn true 33) 30 33 := by
  apply byRun (tile Cn true 33) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_33_27_33 : By (tile Cn true 33) 27 33 := byJoin ctrue_33_27_30 ctrue_33_30_33
lemma ctrue_33_22_33 : By (tile Cn true 33) 22 33 := byJoin ctrue_33_22_27 ctrue_33_27_33
lemma ctrue_33_33_36 : By (tile Cn true 33) 33 36 := by
  apply byRun (tile Cn true 33) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_33_36_39 : By (tile Cn true 33) 36 39 := by
  apply byRun (tile Cn true 33) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_33_33_39 : By (tile Cn true 33) 33 39 := byJoin ctrue_33_33_36 ctrue_33_36_39
lemma ctrue_33_39_42 : By (tile Cn true 33) 39 42 := by
  apply byRun (tile Cn true 33) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_33_42_45 : By (tile Cn true 33) 42 45 := by
  apply byRun (tile Cn true 33) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_33_39_45 : By (tile Cn true 33) 39 45 := byJoin ctrue_33_39_42 ctrue_33_42_45
lemma ctrue_33_33_45 : By (tile Cn true 33) 33 45 := byJoin ctrue_33_33_39 ctrue_33_39_45
lemma ctrue_33_22_45 : By (tile Cn true 33) 22 45 := byJoin ctrue_33_22_33 ctrue_33_33_45
lemma ctrue_33_0_45 : By (tile Cn true 33) 0 45 := byJoin ctrue_33_0_22 ctrue_33_22_45
lemma ctrue_33_45_47 : By (tile Cn true 33) 45 47 := by
  apply byRun (tile Cn true 33) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_33_47_50 : By (tile Cn true 33) 47 50 := by
  apply byRun (tile Cn true 33) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_33_45_50 : By (tile Cn true 33) 45 50 := byJoin ctrue_33_45_47 ctrue_33_47_50
lemma ctrue_33_50_53 : By (tile Cn true 33) 50 53 := by
  apply byRun (tile Cn true 33) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_33_53_56 : By (tile Cn true 33) 53 56 := by
  apply byRun (tile Cn true 33) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_33_50_56 : By (tile Cn true 33) 50 56 := byJoin ctrue_33_50_53 ctrue_33_53_56
lemma ctrue_33_45_56 : By (tile Cn true 33) 45 56 := byJoin ctrue_33_45_50 ctrue_33_50_56
lemma ctrue_33_56_58 : By (tile Cn true 33) 56 58 := by
  apply byRun (tile Cn true 33) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_33_58_61 : By (tile Cn true 33) 58 61 := by
  apply byRun (tile Cn true 33) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_33_56_61 : By (tile Cn true 33) 56 61 := byJoin ctrue_33_56_58 ctrue_33_58_61
lemma ctrue_33_61_64 : By (tile Cn true 33) 61 64 := by
  apply byRun (tile Cn true 33) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_33_64_67 : By (tile Cn true 33) 64 67 := by
  apply byRun (tile Cn true 33) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_33_61_67 : By (tile Cn true 33) 61 67 := byJoin ctrue_33_61_64 ctrue_33_64_67
lemma ctrue_33_56_67 : By (tile Cn true 33) 56 67 := byJoin ctrue_33_56_61 ctrue_33_61_67
lemma ctrue_33_45_67 : By (tile Cn true 33) 45 67 := byJoin ctrue_33_45_56 ctrue_33_56_67
lemma ctrue_33_67_69 : By (tile Cn true 33) 67 69 := by
  apply byRun (tile Cn true 33) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_33_69_72 : By (tile Cn true 33) 69 72 := by
  apply byRun (tile Cn true 33) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_33_67_72 : By (tile Cn true 33) 67 72 := byJoin ctrue_33_67_69 ctrue_33_69_72
lemma ctrue_33_72_75 : By (tile Cn true 33) 72 75 := by
  apply byRun (tile Cn true 33) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_33_75_78 : By (tile Cn true 33) 75 78 := by
  apply byRun (tile Cn true 33) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_33_72_78 : By (tile Cn true 33) 72 78 := byJoin ctrue_33_72_75 ctrue_33_75_78
lemma ctrue_33_67_78 : By (tile Cn true 33) 67 78 := byJoin ctrue_33_67_72 ctrue_33_72_78
lemma ctrue_33_78_81 : By (tile Cn true 33) 78 81 := by
  apply byRun (tile Cn true 33) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_33_81_84 : By (tile Cn true 33) 81 84 := by
  apply byRun (tile Cn true 33) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_33_78_84 : By (tile Cn true 33) 78 84 := byJoin ctrue_33_78_81 ctrue_33_81_84
lemma ctrue_33_84_87 : By (tile Cn true 33) 84 87 := by
  apply byRun (tile Cn true 33) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_33_87_90 : By (tile Cn true 33) 87 90 := by
  apply byRun (tile Cn true 33) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_33_84_90 : By (tile Cn true 33) 84 90 := byJoin ctrue_33_84_87 ctrue_33_87_90
lemma ctrue_33_78_90 : By (tile Cn true 33) 78 90 := byJoin ctrue_33_78_84 ctrue_33_84_90
lemma ctrue_33_67_90 : By (tile Cn true 33) 67 90 := byJoin ctrue_33_67_78 ctrue_33_78_90
lemma ctrue_33_45_90 : By (tile Cn true 33) 45 90 := byJoin ctrue_33_45_67 ctrue_33_67_90
lemma ctrue_33_0_90 : By (tile Cn true 33) 0 90 := byJoin ctrue_33_0_45 ctrue_33_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue34
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_34_0_2 : By (tile Cn true 34) 0 2 := by
  apply byRun (tile Cn true 34) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_34_2_5 : By (tile Cn true 34) 2 5 := by
  apply byRun (tile Cn true 34) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_34_0_5 : By (tile Cn true 34) 0 5 := byJoin ctrue_34_0_2 ctrue_34_2_5
lemma ctrue_34_5_8 : By (tile Cn true 34) 5 8 := by
  apply byRun (tile Cn true 34) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_34_8_11 : By (tile Cn true 34) 8 11 := by
  apply byRun (tile Cn true 34) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_34_5_11 : By (tile Cn true 34) 5 11 := byJoin ctrue_34_5_8 ctrue_34_8_11
lemma ctrue_34_0_11 : By (tile Cn true 34) 0 11 := byJoin ctrue_34_0_5 ctrue_34_5_11
lemma ctrue_34_11_13 : By (tile Cn true 34) 11 13 := by
  apply byRun (tile Cn true 34) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_34_13_16 : By (tile Cn true 34) 13 16 := by
  apply byRun (tile Cn true 34) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_34_11_16 : By (tile Cn true 34) 11 16 := byJoin ctrue_34_11_13 ctrue_34_13_16
lemma ctrue_34_16_19 : By (tile Cn true 34) 16 19 := by
  apply byRun (tile Cn true 34) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_34_19_22 : By (tile Cn true 34) 19 22 := by
  apply byRun (tile Cn true 34) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_34_16_22 : By (tile Cn true 34) 16 22 := byJoin ctrue_34_16_19 ctrue_34_19_22
lemma ctrue_34_11_22 : By (tile Cn true 34) 11 22 := byJoin ctrue_34_11_16 ctrue_34_16_22
lemma ctrue_34_0_22 : By (tile Cn true 34) 0 22 := byJoin ctrue_34_0_11 ctrue_34_11_22
lemma ctrue_34_22_24 : By (tile Cn true 34) 22 24 := by
  apply byRun (tile Cn true 34) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_34_24_27 : By (tile Cn true 34) 24 27 := by
  apply byRun (tile Cn true 34) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_34_22_27 : By (tile Cn true 34) 22 27 := byJoin ctrue_34_22_24 ctrue_34_24_27
lemma ctrue_34_27_30 : By (tile Cn true 34) 27 30 := by
  apply byRun (tile Cn true 34) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_34_30_33 : By (tile Cn true 34) 30 33 := by
  apply byRun (tile Cn true 34) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_34_27_33 : By (tile Cn true 34) 27 33 := byJoin ctrue_34_27_30 ctrue_34_30_33
lemma ctrue_34_22_33 : By (tile Cn true 34) 22 33 := byJoin ctrue_34_22_27 ctrue_34_27_33
lemma ctrue_34_33_36 : By (tile Cn true 34) 33 36 := by
  apply byRun (tile Cn true 34) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_34_36_39 : By (tile Cn true 34) 36 39 := by
  apply byRun (tile Cn true 34) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_34_33_39 : By (tile Cn true 34) 33 39 := byJoin ctrue_34_33_36 ctrue_34_36_39
lemma ctrue_34_39_42 : By (tile Cn true 34) 39 42 := by
  apply byRun (tile Cn true 34) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_34_42_45 : By (tile Cn true 34) 42 45 := by
  apply byRun (tile Cn true 34) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_34_39_45 : By (tile Cn true 34) 39 45 := byJoin ctrue_34_39_42 ctrue_34_42_45
lemma ctrue_34_33_45 : By (tile Cn true 34) 33 45 := byJoin ctrue_34_33_39 ctrue_34_39_45
lemma ctrue_34_22_45 : By (tile Cn true 34) 22 45 := byJoin ctrue_34_22_33 ctrue_34_33_45
lemma ctrue_34_0_45 : By (tile Cn true 34) 0 45 := byJoin ctrue_34_0_22 ctrue_34_22_45
lemma ctrue_34_45_47 : By (tile Cn true 34) 45 47 := by
  apply byRun (tile Cn true 34) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_34_47_50 : By (tile Cn true 34) 47 50 := by
  apply byRun (tile Cn true 34) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_34_45_50 : By (tile Cn true 34) 45 50 := byJoin ctrue_34_45_47 ctrue_34_47_50
lemma ctrue_34_50_53 : By (tile Cn true 34) 50 53 := by
  apply byRun (tile Cn true 34) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_34_53_56 : By (tile Cn true 34) 53 56 := by
  apply byRun (tile Cn true 34) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_34_50_56 : By (tile Cn true 34) 50 56 := byJoin ctrue_34_50_53 ctrue_34_53_56
lemma ctrue_34_45_56 : By (tile Cn true 34) 45 56 := byJoin ctrue_34_45_50 ctrue_34_50_56
lemma ctrue_34_56_58 : By (tile Cn true 34) 56 58 := by
  apply byRun (tile Cn true 34) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_34_58_61 : By (tile Cn true 34) 58 61 := by
  apply byRun (tile Cn true 34) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_34_56_61 : By (tile Cn true 34) 56 61 := byJoin ctrue_34_56_58 ctrue_34_58_61
lemma ctrue_34_61_64 : By (tile Cn true 34) 61 64 := by
  apply byRun (tile Cn true 34) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_34_64_67 : By (tile Cn true 34) 64 67 := by
  apply byRun (tile Cn true 34) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_34_61_67 : By (tile Cn true 34) 61 67 := byJoin ctrue_34_61_64 ctrue_34_64_67
lemma ctrue_34_56_67 : By (tile Cn true 34) 56 67 := byJoin ctrue_34_56_61 ctrue_34_61_67
lemma ctrue_34_45_67 : By (tile Cn true 34) 45 67 := byJoin ctrue_34_45_56 ctrue_34_56_67
lemma ctrue_34_67_69 : By (tile Cn true 34) 67 69 := by
  apply byRun (tile Cn true 34) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_34_69_72 : By (tile Cn true 34) 69 72 := by
  apply byRun (tile Cn true 34) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_34_67_72 : By (tile Cn true 34) 67 72 := byJoin ctrue_34_67_69 ctrue_34_69_72
lemma ctrue_34_72_75 : By (tile Cn true 34) 72 75 := by
  apply byRun (tile Cn true 34) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_34_75_78 : By (tile Cn true 34) 75 78 := by
  apply byRun (tile Cn true 34) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_34_72_78 : By (tile Cn true 34) 72 78 := byJoin ctrue_34_72_75 ctrue_34_75_78
lemma ctrue_34_67_78 : By (tile Cn true 34) 67 78 := byJoin ctrue_34_67_72 ctrue_34_72_78
lemma ctrue_34_78_81 : By (tile Cn true 34) 78 81 := by
  apply byRun (tile Cn true 34) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_34_81_84 : By (tile Cn true 34) 81 84 := by
  apply byRun (tile Cn true 34) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_34_78_84 : By (tile Cn true 34) 78 84 := byJoin ctrue_34_78_81 ctrue_34_81_84
lemma ctrue_34_84_87 : By (tile Cn true 34) 84 87 := by
  apply byRun (tile Cn true 34) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_34_87_90 : By (tile Cn true 34) 87 90 := by
  apply byRun (tile Cn true 34) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_34_84_90 : By (tile Cn true 34) 84 90 := byJoin ctrue_34_84_87 ctrue_34_87_90
lemma ctrue_34_78_90 : By (tile Cn true 34) 78 90 := byJoin ctrue_34_78_84 ctrue_34_84_90
lemma ctrue_34_67_90 : By (tile Cn true 34) 67 90 := byJoin ctrue_34_67_78 ctrue_34_78_90
lemma ctrue_34_45_90 : By (tile Cn true 34) 45 90 := byJoin ctrue_34_45_67 ctrue_34_67_90
lemma ctrue_34_0_90 : By (tile Cn true 34) 0 90 := byJoin ctrue_34_0_45 ctrue_34_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Good
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma gtrue_oai: GoodS Cn true := by
  intro i hi; interval_cases i
  · exact ctrue_0_0_90
  · exact ctrue_1_0_90
  · exact ctrue_2_0_90
  · exact ctrue_3_0_90
  · exact ctrue_4_0_90
  · exact ctrue_5_0_90
  · exact ctrue_6_0_90
  · exact ctrue_7_0_90
  · exact ctrue_8_0_90
  · exact ctrue_9_0_90
  · exact ctrue_10_0_90
  · exact ctrue_11_0_90
  · exact ctrue_12_0_90
  · exact ctrue_13_0_90
  · exact ctrue_14_0_90
  · exact ctrue_15_0_90
  · exact ctrue_16_0_90
  · exact ctrue_17_0_90
  · exact ctrue_18_0_90
  · exact ctrue_19_0_90
  · exact ctrue_20_0_90
  · exact ctrue_21_0_90
  · exact ctrue_22_0_90
  · exact ctrue_23_0_90
  · exact ctrue_24_0_90
  · exact ctrue_25_0_90
  · exact ctrue_26_0_90
  · exact ctrue_27_0_90
  · exact ctrue_28_0_90
  · exact ctrue_29_0_90
  · exact ctrue_30_0_90
  · exact ctrue_31_0_90
  · exact ctrue_32_0_90
  · exact ctrue_33_0_90
  · exact ctrue_34_0_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Mid.Tab.gtrue_oai := @OAI.GeneralMahler.SCal.Mid.Tab.gtrue_oai
