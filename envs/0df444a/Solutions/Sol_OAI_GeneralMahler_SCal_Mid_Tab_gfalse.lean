-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Mid.Tab.gfalse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:59:37.573205+00:00
-- url     : https://prove2.me/submissions/3eda844a-ce2f-433c-ad23-25a3531b7a8c

import Mathlib
import Definitions.Def_OAIQ026G002
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_0_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_10_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_11_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_12_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_13_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_14_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_15_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_16_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_17_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_18_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_19_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_1_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_20_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_21_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_22_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_23_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_24_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_25_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_26_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_28_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_2_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_3_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_4_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_5_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_6_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_7_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_8_0_90
import Theorems.Thm_OAI_GeneralMahler_SCal_Mid_Tab_cfalse_9_0_90

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse27
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_27_0_2 : By (tile Cn false 27) 0 2 := by
  apply byRun (tile Cn false 27) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_27_2_5 : By (tile Cn false 27) 2 5 := by
  apply byRun (tile Cn false 27) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_27_0_5 : By (tile Cn false 27) 0 5 := byJoin cfalse_27_0_2 cfalse_27_2_5
lemma cfalse_27_5_8 : By (tile Cn false 27) 5 8 := by
  apply byRun (tile Cn false 27) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_27_8_11 : By (tile Cn false 27) 8 11 := by
  apply byRun (tile Cn false 27) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_27_5_11 : By (tile Cn false 27) 5 11 := byJoin cfalse_27_5_8 cfalse_27_8_11
lemma cfalse_27_0_11 : By (tile Cn false 27) 0 11 := byJoin cfalse_27_0_5 cfalse_27_5_11
lemma cfalse_27_11_13 : By (tile Cn false 27) 11 13 := by
  apply byRun (tile Cn false 27) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_27_13_16 : By (tile Cn false 27) 13 16 := by
  apply byRun (tile Cn false 27) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_27_11_16 : By (tile Cn false 27) 11 16 := byJoin cfalse_27_11_13 cfalse_27_13_16
lemma cfalse_27_16_19 : By (tile Cn false 27) 16 19 := by
  apply byRun (tile Cn false 27) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_27_19_22 : By (tile Cn false 27) 19 22 := by
  apply byRun (tile Cn false 27) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_27_16_22 : By (tile Cn false 27) 16 22 := byJoin cfalse_27_16_19 cfalse_27_19_22
lemma cfalse_27_11_22 : By (tile Cn false 27) 11 22 := byJoin cfalse_27_11_16 cfalse_27_16_22
lemma cfalse_27_0_22 : By (tile Cn false 27) 0 22 := byJoin cfalse_27_0_11 cfalse_27_11_22
lemma cfalse_27_22_24 : By (tile Cn false 27) 22 24 := by
  apply byRun (tile Cn false 27) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_27_24_27 : By (tile Cn false 27) 24 27 := by
  apply byRun (tile Cn false 27) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_27_22_27 : By (tile Cn false 27) 22 27 := byJoin cfalse_27_22_24 cfalse_27_24_27
lemma cfalse_27_27_30 : By (tile Cn false 27) 27 30 := by
  apply byRun (tile Cn false 27) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_27_30_33 : By (tile Cn false 27) 30 33 := by
  apply byRun (tile Cn false 27) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_27_27_33 : By (tile Cn false 27) 27 33 := byJoin cfalse_27_27_30 cfalse_27_30_33
lemma cfalse_27_22_33 : By (tile Cn false 27) 22 33 := byJoin cfalse_27_22_27 cfalse_27_27_33
lemma cfalse_27_33_36 : By (tile Cn false 27) 33 36 := by
  apply byRun (tile Cn false 27) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_27_36_39 : By (tile Cn false 27) 36 39 := by
  apply byRun (tile Cn false 27) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_27_33_39 : By (tile Cn false 27) 33 39 := byJoin cfalse_27_33_36 cfalse_27_36_39
lemma cfalse_27_39_42 : By (tile Cn false 27) 39 42 := by
  apply byRun (tile Cn false 27) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_27_42_45 : By (tile Cn false 27) 42 45 := by
  apply byRun (tile Cn false 27) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_27_39_45 : By (tile Cn false 27) 39 45 := byJoin cfalse_27_39_42 cfalse_27_42_45
lemma cfalse_27_33_45 : By (tile Cn false 27) 33 45 := byJoin cfalse_27_33_39 cfalse_27_39_45
lemma cfalse_27_22_45 : By (tile Cn false 27) 22 45 := byJoin cfalse_27_22_33 cfalse_27_33_45
lemma cfalse_27_0_45 : By (tile Cn false 27) 0 45 := byJoin cfalse_27_0_22 cfalse_27_22_45
lemma cfalse_27_45_47 : By (tile Cn false 27) 45 47 := by
  apply byRun (tile Cn false 27) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_27_47_50 : By (tile Cn false 27) 47 50 := by
  apply byRun (tile Cn false 27) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_27_45_50 : By (tile Cn false 27) 45 50 := byJoin cfalse_27_45_47 cfalse_27_47_50
lemma cfalse_27_50_53 : By (tile Cn false 27) 50 53 := by
  apply byRun (tile Cn false 27) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_27_53_56 : By (tile Cn false 27) 53 56 := by
  apply byRun (tile Cn false 27) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_27_50_56 : By (tile Cn false 27) 50 56 := byJoin cfalse_27_50_53 cfalse_27_53_56
lemma cfalse_27_45_56 : By (tile Cn false 27) 45 56 := byJoin cfalse_27_45_50 cfalse_27_50_56
lemma cfalse_27_56_58 : By (tile Cn false 27) 56 58 := by
  apply byRun (tile Cn false 27) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_27_58_61 : By (tile Cn false 27) 58 61 := by
  apply byRun (tile Cn false 27) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_27_56_61 : By (tile Cn false 27) 56 61 := byJoin cfalse_27_56_58 cfalse_27_58_61
lemma cfalse_27_61_64 : By (tile Cn false 27) 61 64 := by
  apply byRun (tile Cn false 27) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_27_64_67 : By (tile Cn false 27) 64 67 := by
  apply byRun (tile Cn false 27) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_27_61_67 : By (tile Cn false 27) 61 67 := byJoin cfalse_27_61_64 cfalse_27_64_67
lemma cfalse_27_56_67 : By (tile Cn false 27) 56 67 := byJoin cfalse_27_56_61 cfalse_27_61_67
lemma cfalse_27_45_67 : By (tile Cn false 27) 45 67 := byJoin cfalse_27_45_56 cfalse_27_56_67
lemma cfalse_27_67_69 : By (tile Cn false 27) 67 69 := by
  apply byRun (tile Cn false 27) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_27_69_72 : By (tile Cn false 27) 69 72 := by
  apply byRun (tile Cn false 27) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_27_67_72 : By (tile Cn false 27) 67 72 := byJoin cfalse_27_67_69 cfalse_27_69_72
lemma cfalse_27_72_75 : By (tile Cn false 27) 72 75 := by
  apply byRun (tile Cn false 27) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_27_75_78 : By (tile Cn false 27) 75 78 := by
  apply byRun (tile Cn false 27) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_27_72_78 : By (tile Cn false 27) 72 78 := byJoin cfalse_27_72_75 cfalse_27_75_78
lemma cfalse_27_67_78 : By (tile Cn false 27) 67 78 := byJoin cfalse_27_67_72 cfalse_27_72_78
lemma cfalse_27_78_81 : By (tile Cn false 27) 78 81 := by
  apply byRun (tile Cn false 27) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_27_81_84 : By (tile Cn false 27) 81 84 := by
  apply byRun (tile Cn false 27) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_27_78_84 : By (tile Cn false 27) 78 84 := byJoin cfalse_27_78_81 cfalse_27_81_84
lemma cfalse_27_84_87 : By (tile Cn false 27) 84 87 := by
  apply byRun (tile Cn false 27) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_27_87_90 : By (tile Cn false 27) 87 90 := by
  apply byRun (tile Cn false 27) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_27_84_90 : By (tile Cn false 27) 84 90 := byJoin cfalse_27_84_87 cfalse_27_87_90
lemma cfalse_27_78_90 : By (tile Cn false 27) 78 90 := byJoin cfalse_27_78_84 cfalse_27_84_90
lemma cfalse_27_67_90 : By (tile Cn false 27) 67 90 := byJoin cfalse_27_67_78 cfalse_27_78_90
lemma cfalse_27_45_90 : By (tile Cn false 27) 45 90 := byJoin cfalse_27_45_67 cfalse_27_67_90
lemma cfalse_27_0_90 : By (tile Cn false 27) 0 90 := byJoin cfalse_27_0_45 cfalse_27_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse29
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_29_0_2 : By (tile Cn false 29) 0 2 := by
  apply byRun (tile Cn false 29) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_29_2_5 : By (tile Cn false 29) 2 5 := by
  apply byRun (tile Cn false 29) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_29_0_5 : By (tile Cn false 29) 0 5 := byJoin cfalse_29_0_2 cfalse_29_2_5
lemma cfalse_29_5_8 : By (tile Cn false 29) 5 8 := by
  apply byRun (tile Cn false 29) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_29_8_11 : By (tile Cn false 29) 8 11 := by
  apply byRun (tile Cn false 29) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_29_5_11 : By (tile Cn false 29) 5 11 := byJoin cfalse_29_5_8 cfalse_29_8_11
lemma cfalse_29_0_11 : By (tile Cn false 29) 0 11 := byJoin cfalse_29_0_5 cfalse_29_5_11
lemma cfalse_29_11_13 : By (tile Cn false 29) 11 13 := by
  apply byRun (tile Cn false 29) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_29_13_16 : By (tile Cn false 29) 13 16 := by
  apply byRun (tile Cn false 29) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_29_11_16 : By (tile Cn false 29) 11 16 := byJoin cfalse_29_11_13 cfalse_29_13_16
lemma cfalse_29_16_19 : By (tile Cn false 29) 16 19 := by
  apply byRun (tile Cn false 29) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_29_19_22 : By (tile Cn false 29) 19 22 := by
  apply byRun (tile Cn false 29) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_29_16_22 : By (tile Cn false 29) 16 22 := byJoin cfalse_29_16_19 cfalse_29_19_22
lemma cfalse_29_11_22 : By (tile Cn false 29) 11 22 := byJoin cfalse_29_11_16 cfalse_29_16_22
lemma cfalse_29_0_22 : By (tile Cn false 29) 0 22 := byJoin cfalse_29_0_11 cfalse_29_11_22
lemma cfalse_29_22_24 : By (tile Cn false 29) 22 24 := by
  apply byRun (tile Cn false 29) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_29_24_27 : By (tile Cn false 29) 24 27 := by
  apply byRun (tile Cn false 29) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_29_22_27 : By (tile Cn false 29) 22 27 := byJoin cfalse_29_22_24 cfalse_29_24_27
lemma cfalse_29_27_30 : By (tile Cn false 29) 27 30 := by
  apply byRun (tile Cn false 29) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_29_30_33 : By (tile Cn false 29) 30 33 := by
  apply byRun (tile Cn false 29) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_29_27_33 : By (tile Cn false 29) 27 33 := byJoin cfalse_29_27_30 cfalse_29_30_33
lemma cfalse_29_22_33 : By (tile Cn false 29) 22 33 := byJoin cfalse_29_22_27 cfalse_29_27_33
lemma cfalse_29_33_36 : By (tile Cn false 29) 33 36 := by
  apply byRun (tile Cn false 29) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_29_36_39 : By (tile Cn false 29) 36 39 := by
  apply byRun (tile Cn false 29) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_29_33_39 : By (tile Cn false 29) 33 39 := byJoin cfalse_29_33_36 cfalse_29_36_39
lemma cfalse_29_39_42 : By (tile Cn false 29) 39 42 := by
  apply byRun (tile Cn false 29) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_29_42_45 : By (tile Cn false 29) 42 45 := by
  apply byRun (tile Cn false 29) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_29_39_45 : By (tile Cn false 29) 39 45 := byJoin cfalse_29_39_42 cfalse_29_42_45
lemma cfalse_29_33_45 : By (tile Cn false 29) 33 45 := byJoin cfalse_29_33_39 cfalse_29_39_45
lemma cfalse_29_22_45 : By (tile Cn false 29) 22 45 := byJoin cfalse_29_22_33 cfalse_29_33_45
lemma cfalse_29_0_45 : By (tile Cn false 29) 0 45 := byJoin cfalse_29_0_22 cfalse_29_22_45
lemma cfalse_29_45_47 : By (tile Cn false 29) 45 47 := by
  apply byRun (tile Cn false 29) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_29_47_50 : By (tile Cn false 29) 47 50 := by
  apply byRun (tile Cn false 29) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_29_45_50 : By (tile Cn false 29) 45 50 := byJoin cfalse_29_45_47 cfalse_29_47_50
lemma cfalse_29_50_53 : By (tile Cn false 29) 50 53 := by
  apply byRun (tile Cn false 29) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_29_53_56 : By (tile Cn false 29) 53 56 := by
  apply byRun (tile Cn false 29) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_29_50_56 : By (tile Cn false 29) 50 56 := byJoin cfalse_29_50_53 cfalse_29_53_56
lemma cfalse_29_45_56 : By (tile Cn false 29) 45 56 := byJoin cfalse_29_45_50 cfalse_29_50_56
lemma cfalse_29_56_58 : By (tile Cn false 29) 56 58 := by
  apply byRun (tile Cn false 29) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_29_58_61 : By (tile Cn false 29) 58 61 := by
  apply byRun (tile Cn false 29) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_29_56_61 : By (tile Cn false 29) 56 61 := byJoin cfalse_29_56_58 cfalse_29_58_61
lemma cfalse_29_61_64 : By (tile Cn false 29) 61 64 := by
  apply byRun (tile Cn false 29) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_29_64_67 : By (tile Cn false 29) 64 67 := by
  apply byRun (tile Cn false 29) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_29_61_67 : By (tile Cn false 29) 61 67 := byJoin cfalse_29_61_64 cfalse_29_64_67
lemma cfalse_29_56_67 : By (tile Cn false 29) 56 67 := byJoin cfalse_29_56_61 cfalse_29_61_67
lemma cfalse_29_45_67 : By (tile Cn false 29) 45 67 := byJoin cfalse_29_45_56 cfalse_29_56_67
lemma cfalse_29_67_69 : By (tile Cn false 29) 67 69 := by
  apply byRun (tile Cn false 29) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_29_69_72 : By (tile Cn false 29) 69 72 := by
  apply byRun (tile Cn false 29) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_29_67_72 : By (tile Cn false 29) 67 72 := byJoin cfalse_29_67_69 cfalse_29_69_72
lemma cfalse_29_72_75 : By (tile Cn false 29) 72 75 := by
  apply byRun (tile Cn false 29) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_29_75_78 : By (tile Cn false 29) 75 78 := by
  apply byRun (tile Cn false 29) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_29_72_78 : By (tile Cn false 29) 72 78 := byJoin cfalse_29_72_75 cfalse_29_75_78
lemma cfalse_29_67_78 : By (tile Cn false 29) 67 78 := byJoin cfalse_29_67_72 cfalse_29_72_78
lemma cfalse_29_78_81 : By (tile Cn false 29) 78 81 := by
  apply byRun (tile Cn false 29) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_29_81_84 : By (tile Cn false 29) 81 84 := by
  apply byRun (tile Cn false 29) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_29_78_84 : By (tile Cn false 29) 78 84 := byJoin cfalse_29_78_81 cfalse_29_81_84
lemma cfalse_29_84_87 : By (tile Cn false 29) 84 87 := by
  apply byRun (tile Cn false 29) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_29_87_90 : By (tile Cn false 29) 87 90 := by
  apply byRun (tile Cn false 29) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_29_84_90 : By (tile Cn false 29) 84 90 := byJoin cfalse_29_84_87 cfalse_29_87_90
lemma cfalse_29_78_90 : By (tile Cn false 29) 78 90 := byJoin cfalse_29_78_84 cfalse_29_84_90
lemma cfalse_29_67_90 : By (tile Cn false 29) 67 90 := byJoin cfalse_29_67_78 cfalse_29_78_90
lemma cfalse_29_45_90 : By (tile Cn false 29) 45 90 := byJoin cfalse_29_45_67 cfalse_29_67_90
lemma cfalse_29_0_90 : By (tile Cn false 29) 0 90 := byJoin cfalse_29_0_45 cfalse_29_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse30
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_30_0_2 : By (tile Cn false 30) 0 2 := by
  apply byRun (tile Cn false 30) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_30_2_5 : By (tile Cn false 30) 2 5 := by
  apply byRun (tile Cn false 30) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_30_0_5 : By (tile Cn false 30) 0 5 := byJoin cfalse_30_0_2 cfalse_30_2_5
lemma cfalse_30_5_8 : By (tile Cn false 30) 5 8 := by
  apply byRun (tile Cn false 30) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_30_8_11 : By (tile Cn false 30) 8 11 := by
  apply byRun (tile Cn false 30) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_30_5_11 : By (tile Cn false 30) 5 11 := byJoin cfalse_30_5_8 cfalse_30_8_11
lemma cfalse_30_0_11 : By (tile Cn false 30) 0 11 := byJoin cfalse_30_0_5 cfalse_30_5_11
lemma cfalse_30_11_13 : By (tile Cn false 30) 11 13 := by
  apply byRun (tile Cn false 30) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_30_13_16 : By (tile Cn false 30) 13 16 := by
  apply byRun (tile Cn false 30) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_30_11_16 : By (tile Cn false 30) 11 16 := byJoin cfalse_30_11_13 cfalse_30_13_16
lemma cfalse_30_16_19 : By (tile Cn false 30) 16 19 := by
  apply byRun (tile Cn false 30) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_30_19_22 : By (tile Cn false 30) 19 22 := by
  apply byRun (tile Cn false 30) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_30_16_22 : By (tile Cn false 30) 16 22 := byJoin cfalse_30_16_19 cfalse_30_19_22
lemma cfalse_30_11_22 : By (tile Cn false 30) 11 22 := byJoin cfalse_30_11_16 cfalse_30_16_22
lemma cfalse_30_0_22 : By (tile Cn false 30) 0 22 := byJoin cfalse_30_0_11 cfalse_30_11_22
lemma cfalse_30_22_24 : By (tile Cn false 30) 22 24 := by
  apply byRun (tile Cn false 30) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_30_24_27 : By (tile Cn false 30) 24 27 := by
  apply byRun (tile Cn false 30) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_30_22_27 : By (tile Cn false 30) 22 27 := byJoin cfalse_30_22_24 cfalse_30_24_27
lemma cfalse_30_27_30 : By (tile Cn false 30) 27 30 := by
  apply byRun (tile Cn false 30) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_30_30_33 : By (tile Cn false 30) 30 33 := by
  apply byRun (tile Cn false 30) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_30_27_33 : By (tile Cn false 30) 27 33 := byJoin cfalse_30_27_30 cfalse_30_30_33
lemma cfalse_30_22_33 : By (tile Cn false 30) 22 33 := byJoin cfalse_30_22_27 cfalse_30_27_33
lemma cfalse_30_33_36 : By (tile Cn false 30) 33 36 := by
  apply byRun (tile Cn false 30) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_30_36_39 : By (tile Cn false 30) 36 39 := by
  apply byRun (tile Cn false 30) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_30_33_39 : By (tile Cn false 30) 33 39 := byJoin cfalse_30_33_36 cfalse_30_36_39
lemma cfalse_30_39_42 : By (tile Cn false 30) 39 42 := by
  apply byRun (tile Cn false 30) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_30_42_45 : By (tile Cn false 30) 42 45 := by
  apply byRun (tile Cn false 30) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_30_39_45 : By (tile Cn false 30) 39 45 := byJoin cfalse_30_39_42 cfalse_30_42_45
lemma cfalse_30_33_45 : By (tile Cn false 30) 33 45 := byJoin cfalse_30_33_39 cfalse_30_39_45
lemma cfalse_30_22_45 : By (tile Cn false 30) 22 45 := byJoin cfalse_30_22_33 cfalse_30_33_45
lemma cfalse_30_0_45 : By (tile Cn false 30) 0 45 := byJoin cfalse_30_0_22 cfalse_30_22_45
lemma cfalse_30_45_47 : By (tile Cn false 30) 45 47 := by
  apply byRun (tile Cn false 30) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_30_47_50 : By (tile Cn false 30) 47 50 := by
  apply byRun (tile Cn false 30) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_30_45_50 : By (tile Cn false 30) 45 50 := byJoin cfalse_30_45_47 cfalse_30_47_50
lemma cfalse_30_50_53 : By (tile Cn false 30) 50 53 := by
  apply byRun (tile Cn false 30) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_30_53_56 : By (tile Cn false 30) 53 56 := by
  apply byRun (tile Cn false 30) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_30_50_56 : By (tile Cn false 30) 50 56 := byJoin cfalse_30_50_53 cfalse_30_53_56
lemma cfalse_30_45_56 : By (tile Cn false 30) 45 56 := byJoin cfalse_30_45_50 cfalse_30_50_56
lemma cfalse_30_56_58 : By (tile Cn false 30) 56 58 := by
  apply byRun (tile Cn false 30) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_30_58_61 : By (tile Cn false 30) 58 61 := by
  apply byRun (tile Cn false 30) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_30_56_61 : By (tile Cn false 30) 56 61 := byJoin cfalse_30_56_58 cfalse_30_58_61
lemma cfalse_30_61_64 : By (tile Cn false 30) 61 64 := by
  apply byRun (tile Cn false 30) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_30_64_67 : By (tile Cn false 30) 64 67 := by
  apply byRun (tile Cn false 30) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_30_61_67 : By (tile Cn false 30) 61 67 := byJoin cfalse_30_61_64 cfalse_30_64_67
lemma cfalse_30_56_67 : By (tile Cn false 30) 56 67 := byJoin cfalse_30_56_61 cfalse_30_61_67
lemma cfalse_30_45_67 : By (tile Cn false 30) 45 67 := byJoin cfalse_30_45_56 cfalse_30_56_67
lemma cfalse_30_67_69 : By (tile Cn false 30) 67 69 := by
  apply byRun (tile Cn false 30) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_30_69_72 : By (tile Cn false 30) 69 72 := by
  apply byRun (tile Cn false 30) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_30_67_72 : By (tile Cn false 30) 67 72 := byJoin cfalse_30_67_69 cfalse_30_69_72
lemma cfalse_30_72_75 : By (tile Cn false 30) 72 75 := by
  apply byRun (tile Cn false 30) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_30_75_78 : By (tile Cn false 30) 75 78 := by
  apply byRun (tile Cn false 30) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_30_72_78 : By (tile Cn false 30) 72 78 := byJoin cfalse_30_72_75 cfalse_30_75_78
lemma cfalse_30_67_78 : By (tile Cn false 30) 67 78 := byJoin cfalse_30_67_72 cfalse_30_72_78
lemma cfalse_30_78_81 : By (tile Cn false 30) 78 81 := by
  apply byRun (tile Cn false 30) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_30_81_84 : By (tile Cn false 30) 81 84 := by
  apply byRun (tile Cn false 30) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_30_78_84 : By (tile Cn false 30) 78 84 := byJoin cfalse_30_78_81 cfalse_30_81_84
lemma cfalse_30_84_87 : By (tile Cn false 30) 84 87 := by
  apply byRun (tile Cn false 30) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_30_87_90 : By (tile Cn false 30) 87 90 := by
  apply byRun (tile Cn false 30) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_30_84_90 : By (tile Cn false 30) 84 90 := byJoin cfalse_30_84_87 cfalse_30_87_90
lemma cfalse_30_78_90 : By (tile Cn false 30) 78 90 := byJoin cfalse_30_78_84 cfalse_30_84_90
lemma cfalse_30_67_90 : By (tile Cn false 30) 67 90 := byJoin cfalse_30_67_78 cfalse_30_78_90
lemma cfalse_30_45_90 : By (tile Cn false 30) 45 90 := byJoin cfalse_30_45_67 cfalse_30_67_90
lemma cfalse_30_0_90 : By (tile Cn false 30) 0 90 := byJoin cfalse_30_0_45 cfalse_30_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse31
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_31_0_2 : By (tile Cn false 31) 0 2 := by
  apply byRun (tile Cn false 31) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_31_2_5 : By (tile Cn false 31) 2 5 := by
  apply byRun (tile Cn false 31) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_31_0_5 : By (tile Cn false 31) 0 5 := byJoin cfalse_31_0_2 cfalse_31_2_5
lemma cfalse_31_5_8 : By (tile Cn false 31) 5 8 := by
  apply byRun (tile Cn false 31) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_31_8_11 : By (tile Cn false 31) 8 11 := by
  apply byRun (tile Cn false 31) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_31_5_11 : By (tile Cn false 31) 5 11 := byJoin cfalse_31_5_8 cfalse_31_8_11
lemma cfalse_31_0_11 : By (tile Cn false 31) 0 11 := byJoin cfalse_31_0_5 cfalse_31_5_11
lemma cfalse_31_11_13 : By (tile Cn false 31) 11 13 := by
  apply byRun (tile Cn false 31) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_31_13_16 : By (tile Cn false 31) 13 16 := by
  apply byRun (tile Cn false 31) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_31_11_16 : By (tile Cn false 31) 11 16 := byJoin cfalse_31_11_13 cfalse_31_13_16
lemma cfalse_31_16_19 : By (tile Cn false 31) 16 19 := by
  apply byRun (tile Cn false 31) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_31_19_22 : By (tile Cn false 31) 19 22 := by
  apply byRun (tile Cn false 31) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_31_16_22 : By (tile Cn false 31) 16 22 := byJoin cfalse_31_16_19 cfalse_31_19_22
lemma cfalse_31_11_22 : By (tile Cn false 31) 11 22 := byJoin cfalse_31_11_16 cfalse_31_16_22
lemma cfalse_31_0_22 : By (tile Cn false 31) 0 22 := byJoin cfalse_31_0_11 cfalse_31_11_22
lemma cfalse_31_22_24 : By (tile Cn false 31) 22 24 := by
  apply byRun (tile Cn false 31) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_31_24_27 : By (tile Cn false 31) 24 27 := by
  apply byRun (tile Cn false 31) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_31_22_27 : By (tile Cn false 31) 22 27 := byJoin cfalse_31_22_24 cfalse_31_24_27
lemma cfalse_31_27_30 : By (tile Cn false 31) 27 30 := by
  apply byRun (tile Cn false 31) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_31_30_33 : By (tile Cn false 31) 30 33 := by
  apply byRun (tile Cn false 31) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_31_27_33 : By (tile Cn false 31) 27 33 := byJoin cfalse_31_27_30 cfalse_31_30_33
lemma cfalse_31_22_33 : By (tile Cn false 31) 22 33 := byJoin cfalse_31_22_27 cfalse_31_27_33
lemma cfalse_31_33_36 : By (tile Cn false 31) 33 36 := by
  apply byRun (tile Cn false 31) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_31_36_39 : By (tile Cn false 31) 36 39 := by
  apply byRun (tile Cn false 31) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_31_33_39 : By (tile Cn false 31) 33 39 := byJoin cfalse_31_33_36 cfalse_31_36_39
lemma cfalse_31_39_42 : By (tile Cn false 31) 39 42 := by
  apply byRun (tile Cn false 31) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_31_42_45 : By (tile Cn false 31) 42 45 := by
  apply byRun (tile Cn false 31) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_31_39_45 : By (tile Cn false 31) 39 45 := byJoin cfalse_31_39_42 cfalse_31_42_45
lemma cfalse_31_33_45 : By (tile Cn false 31) 33 45 := byJoin cfalse_31_33_39 cfalse_31_39_45
lemma cfalse_31_22_45 : By (tile Cn false 31) 22 45 := byJoin cfalse_31_22_33 cfalse_31_33_45
lemma cfalse_31_0_45 : By (tile Cn false 31) 0 45 := byJoin cfalse_31_0_22 cfalse_31_22_45
lemma cfalse_31_45_47 : By (tile Cn false 31) 45 47 := by
  apply byRun (tile Cn false 31) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_31_47_50 : By (tile Cn false 31) 47 50 := by
  apply byRun (tile Cn false 31) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_31_45_50 : By (tile Cn false 31) 45 50 := byJoin cfalse_31_45_47 cfalse_31_47_50
lemma cfalse_31_50_53 : By (tile Cn false 31) 50 53 := by
  apply byRun (tile Cn false 31) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_31_53_56 : By (tile Cn false 31) 53 56 := by
  apply byRun (tile Cn false 31) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_31_50_56 : By (tile Cn false 31) 50 56 := byJoin cfalse_31_50_53 cfalse_31_53_56
lemma cfalse_31_45_56 : By (tile Cn false 31) 45 56 := byJoin cfalse_31_45_50 cfalse_31_50_56
lemma cfalse_31_56_58 : By (tile Cn false 31) 56 58 := by
  apply byRun (tile Cn false 31) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_31_58_61 : By (tile Cn false 31) 58 61 := by
  apply byRun (tile Cn false 31) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_31_56_61 : By (tile Cn false 31) 56 61 := byJoin cfalse_31_56_58 cfalse_31_58_61
lemma cfalse_31_61_64 : By (tile Cn false 31) 61 64 := by
  apply byRun (tile Cn false 31) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_31_64_67 : By (tile Cn false 31) 64 67 := by
  apply byRun (tile Cn false 31) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_31_61_67 : By (tile Cn false 31) 61 67 := byJoin cfalse_31_61_64 cfalse_31_64_67
lemma cfalse_31_56_67 : By (tile Cn false 31) 56 67 := byJoin cfalse_31_56_61 cfalse_31_61_67
lemma cfalse_31_45_67 : By (tile Cn false 31) 45 67 := byJoin cfalse_31_45_56 cfalse_31_56_67
lemma cfalse_31_67_69 : By (tile Cn false 31) 67 69 := by
  apply byRun (tile Cn false 31) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_31_69_72 : By (tile Cn false 31) 69 72 := by
  apply byRun (tile Cn false 31) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_31_67_72 : By (tile Cn false 31) 67 72 := byJoin cfalse_31_67_69 cfalse_31_69_72
lemma cfalse_31_72_75 : By (tile Cn false 31) 72 75 := by
  apply byRun (tile Cn false 31) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_31_75_78 : By (tile Cn false 31) 75 78 := by
  apply byRun (tile Cn false 31) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_31_72_78 : By (tile Cn false 31) 72 78 := byJoin cfalse_31_72_75 cfalse_31_75_78
lemma cfalse_31_67_78 : By (tile Cn false 31) 67 78 := byJoin cfalse_31_67_72 cfalse_31_72_78
lemma cfalse_31_78_81 : By (tile Cn false 31) 78 81 := by
  apply byRun (tile Cn false 31) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_31_81_84 : By (tile Cn false 31) 81 84 := by
  apply byRun (tile Cn false 31) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_31_78_84 : By (tile Cn false 31) 78 84 := byJoin cfalse_31_78_81 cfalse_31_81_84
lemma cfalse_31_84_87 : By (tile Cn false 31) 84 87 := by
  apply byRun (tile Cn false 31) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_31_87_90 : By (tile Cn false 31) 87 90 := by
  apply byRun (tile Cn false 31) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_31_84_90 : By (tile Cn false 31) 84 90 := byJoin cfalse_31_84_87 cfalse_31_87_90
lemma cfalse_31_78_90 : By (tile Cn false 31) 78 90 := byJoin cfalse_31_78_84 cfalse_31_84_90
lemma cfalse_31_67_90 : By (tile Cn false 31) 67 90 := byJoin cfalse_31_67_78 cfalse_31_78_90
lemma cfalse_31_45_90 : By (tile Cn false 31) 45 90 := byJoin cfalse_31_45_67 cfalse_31_67_90
lemma cfalse_31_0_90 : By (tile Cn false 31) 0 90 := byJoin cfalse_31_0_45 cfalse_31_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse32
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_32_0_2 : By (tile Cn false 32) 0 2 := by
  apply byRun (tile Cn false 32) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_32_2_5 : By (tile Cn false 32) 2 5 := by
  apply byRun (tile Cn false 32) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_32_0_5 : By (tile Cn false 32) 0 5 := byJoin cfalse_32_0_2 cfalse_32_2_5
lemma cfalse_32_5_8 : By (tile Cn false 32) 5 8 := by
  apply byRun (tile Cn false 32) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_32_8_11 : By (tile Cn false 32) 8 11 := by
  apply byRun (tile Cn false 32) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_32_5_11 : By (tile Cn false 32) 5 11 := byJoin cfalse_32_5_8 cfalse_32_8_11
lemma cfalse_32_0_11 : By (tile Cn false 32) 0 11 := byJoin cfalse_32_0_5 cfalse_32_5_11
lemma cfalse_32_11_13 : By (tile Cn false 32) 11 13 := by
  apply byRun (tile Cn false 32) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_32_13_16 : By (tile Cn false 32) 13 16 := by
  apply byRun (tile Cn false 32) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_32_11_16 : By (tile Cn false 32) 11 16 := byJoin cfalse_32_11_13 cfalse_32_13_16
lemma cfalse_32_16_19 : By (tile Cn false 32) 16 19 := by
  apply byRun (tile Cn false 32) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_32_19_22 : By (tile Cn false 32) 19 22 := by
  apply byRun (tile Cn false 32) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_32_16_22 : By (tile Cn false 32) 16 22 := byJoin cfalse_32_16_19 cfalse_32_19_22
lemma cfalse_32_11_22 : By (tile Cn false 32) 11 22 := byJoin cfalse_32_11_16 cfalse_32_16_22
lemma cfalse_32_0_22 : By (tile Cn false 32) 0 22 := byJoin cfalse_32_0_11 cfalse_32_11_22
lemma cfalse_32_22_24 : By (tile Cn false 32) 22 24 := by
  apply byRun (tile Cn false 32) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_32_24_27 : By (tile Cn false 32) 24 27 := by
  apply byRun (tile Cn false 32) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_32_22_27 : By (tile Cn false 32) 22 27 := byJoin cfalse_32_22_24 cfalse_32_24_27
lemma cfalse_32_27_30 : By (tile Cn false 32) 27 30 := by
  apply byRun (tile Cn false 32) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_32_30_33 : By (tile Cn false 32) 30 33 := by
  apply byRun (tile Cn false 32) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_32_27_33 : By (tile Cn false 32) 27 33 := byJoin cfalse_32_27_30 cfalse_32_30_33
lemma cfalse_32_22_33 : By (tile Cn false 32) 22 33 := byJoin cfalse_32_22_27 cfalse_32_27_33
lemma cfalse_32_33_36 : By (tile Cn false 32) 33 36 := by
  apply byRun (tile Cn false 32) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_32_36_39 : By (tile Cn false 32) 36 39 := by
  apply byRun (tile Cn false 32) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_32_33_39 : By (tile Cn false 32) 33 39 := byJoin cfalse_32_33_36 cfalse_32_36_39
lemma cfalse_32_39_42 : By (tile Cn false 32) 39 42 := by
  apply byRun (tile Cn false 32) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_32_42_45 : By (tile Cn false 32) 42 45 := by
  apply byRun (tile Cn false 32) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_32_39_45 : By (tile Cn false 32) 39 45 := byJoin cfalse_32_39_42 cfalse_32_42_45
lemma cfalse_32_33_45 : By (tile Cn false 32) 33 45 := byJoin cfalse_32_33_39 cfalse_32_39_45
lemma cfalse_32_22_45 : By (tile Cn false 32) 22 45 := byJoin cfalse_32_22_33 cfalse_32_33_45
lemma cfalse_32_0_45 : By (tile Cn false 32) 0 45 := byJoin cfalse_32_0_22 cfalse_32_22_45
lemma cfalse_32_45_47 : By (tile Cn false 32) 45 47 := by
  apply byRun (tile Cn false 32) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_32_47_50 : By (tile Cn false 32) 47 50 := by
  apply byRun (tile Cn false 32) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_32_45_50 : By (tile Cn false 32) 45 50 := byJoin cfalse_32_45_47 cfalse_32_47_50
lemma cfalse_32_50_53 : By (tile Cn false 32) 50 53 := by
  apply byRun (tile Cn false 32) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_32_53_56 : By (tile Cn false 32) 53 56 := by
  apply byRun (tile Cn false 32) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_32_50_56 : By (tile Cn false 32) 50 56 := byJoin cfalse_32_50_53 cfalse_32_53_56
lemma cfalse_32_45_56 : By (tile Cn false 32) 45 56 := byJoin cfalse_32_45_50 cfalse_32_50_56
lemma cfalse_32_56_58 : By (tile Cn false 32) 56 58 := by
  apply byRun (tile Cn false 32) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_32_58_61 : By (tile Cn false 32) 58 61 := by
  apply byRun (tile Cn false 32) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_32_56_61 : By (tile Cn false 32) 56 61 := byJoin cfalse_32_56_58 cfalse_32_58_61
lemma cfalse_32_61_64 : By (tile Cn false 32) 61 64 := by
  apply byRun (tile Cn false 32) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_32_64_67 : By (tile Cn false 32) 64 67 := by
  apply byRun (tile Cn false 32) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_32_61_67 : By (tile Cn false 32) 61 67 := byJoin cfalse_32_61_64 cfalse_32_64_67
lemma cfalse_32_56_67 : By (tile Cn false 32) 56 67 := byJoin cfalse_32_56_61 cfalse_32_61_67
lemma cfalse_32_45_67 : By (tile Cn false 32) 45 67 := byJoin cfalse_32_45_56 cfalse_32_56_67
lemma cfalse_32_67_69 : By (tile Cn false 32) 67 69 := by
  apply byRun (tile Cn false 32) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_32_69_72 : By (tile Cn false 32) 69 72 := by
  apply byRun (tile Cn false 32) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_32_67_72 : By (tile Cn false 32) 67 72 := byJoin cfalse_32_67_69 cfalse_32_69_72
lemma cfalse_32_72_75 : By (tile Cn false 32) 72 75 := by
  apply byRun (tile Cn false 32) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_32_75_78 : By (tile Cn false 32) 75 78 := by
  apply byRun (tile Cn false 32) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_32_72_78 : By (tile Cn false 32) 72 78 := byJoin cfalse_32_72_75 cfalse_32_75_78
lemma cfalse_32_67_78 : By (tile Cn false 32) 67 78 := byJoin cfalse_32_67_72 cfalse_32_72_78
lemma cfalse_32_78_81 : By (tile Cn false 32) 78 81 := by
  apply byRun (tile Cn false 32) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_32_81_84 : By (tile Cn false 32) 81 84 := by
  apply byRun (tile Cn false 32) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_32_78_84 : By (tile Cn false 32) 78 84 := byJoin cfalse_32_78_81 cfalse_32_81_84
lemma cfalse_32_84_87 : By (tile Cn false 32) 84 87 := by
  apply byRun (tile Cn false 32) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_32_87_90 : By (tile Cn false 32) 87 90 := by
  apply byRun (tile Cn false 32) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_32_84_90 : By (tile Cn false 32) 84 90 := byJoin cfalse_32_84_87 cfalse_32_87_90
lemma cfalse_32_78_90 : By (tile Cn false 32) 78 90 := byJoin cfalse_32_78_84 cfalse_32_84_90
lemma cfalse_32_67_90 : By (tile Cn false 32) 67 90 := byJoin cfalse_32_67_78 cfalse_32_78_90
lemma cfalse_32_45_90 : By (tile Cn false 32) 45 90 := byJoin cfalse_32_45_67 cfalse_32_67_90
lemma cfalse_32_0_90 : By (tile Cn false 32) 0 90 := byJoin cfalse_32_0_45 cfalse_32_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse33
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_33_0_2 : By (tile Cn false 33) 0 2 := by
  apply byRun (tile Cn false 33) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_33_2_5 : By (tile Cn false 33) 2 5 := by
  apply byRun (tile Cn false 33) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_33_0_5 : By (tile Cn false 33) 0 5 := byJoin cfalse_33_0_2 cfalse_33_2_5
lemma cfalse_33_5_8 : By (tile Cn false 33) 5 8 := by
  apply byRun (tile Cn false 33) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_33_8_11 : By (tile Cn false 33) 8 11 := by
  apply byRun (tile Cn false 33) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_33_5_11 : By (tile Cn false 33) 5 11 := byJoin cfalse_33_5_8 cfalse_33_8_11
lemma cfalse_33_0_11 : By (tile Cn false 33) 0 11 := byJoin cfalse_33_0_5 cfalse_33_5_11
lemma cfalse_33_11_13 : By (tile Cn false 33) 11 13 := by
  apply byRun (tile Cn false 33) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_33_13_16 : By (tile Cn false 33) 13 16 := by
  apply byRun (tile Cn false 33) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_33_11_16 : By (tile Cn false 33) 11 16 := byJoin cfalse_33_11_13 cfalse_33_13_16
lemma cfalse_33_16_19 : By (tile Cn false 33) 16 19 := by
  apply byRun (tile Cn false 33) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_33_19_22 : By (tile Cn false 33) 19 22 := by
  apply byRun (tile Cn false 33) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_33_16_22 : By (tile Cn false 33) 16 22 := byJoin cfalse_33_16_19 cfalse_33_19_22
lemma cfalse_33_11_22 : By (tile Cn false 33) 11 22 := byJoin cfalse_33_11_16 cfalse_33_16_22
lemma cfalse_33_0_22 : By (tile Cn false 33) 0 22 := byJoin cfalse_33_0_11 cfalse_33_11_22
lemma cfalse_33_22_24 : By (tile Cn false 33) 22 24 := by
  apply byRun (tile Cn false 33) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_33_24_27 : By (tile Cn false 33) 24 27 := by
  apply byRun (tile Cn false 33) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_33_22_27 : By (tile Cn false 33) 22 27 := byJoin cfalse_33_22_24 cfalse_33_24_27
lemma cfalse_33_27_30 : By (tile Cn false 33) 27 30 := by
  apply byRun (tile Cn false 33) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_33_30_33 : By (tile Cn false 33) 30 33 := by
  apply byRun (tile Cn false 33) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_33_27_33 : By (tile Cn false 33) 27 33 := byJoin cfalse_33_27_30 cfalse_33_30_33
lemma cfalse_33_22_33 : By (tile Cn false 33) 22 33 := byJoin cfalse_33_22_27 cfalse_33_27_33
lemma cfalse_33_33_36 : By (tile Cn false 33) 33 36 := by
  apply byRun (tile Cn false 33) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_33_36_39 : By (tile Cn false 33) 36 39 := by
  apply byRun (tile Cn false 33) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_33_33_39 : By (tile Cn false 33) 33 39 := byJoin cfalse_33_33_36 cfalse_33_36_39
lemma cfalse_33_39_42 : By (tile Cn false 33) 39 42 := by
  apply byRun (tile Cn false 33) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_33_42_45 : By (tile Cn false 33) 42 45 := by
  apply byRun (tile Cn false 33) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_33_39_45 : By (tile Cn false 33) 39 45 := byJoin cfalse_33_39_42 cfalse_33_42_45
lemma cfalse_33_33_45 : By (tile Cn false 33) 33 45 := byJoin cfalse_33_33_39 cfalse_33_39_45
lemma cfalse_33_22_45 : By (tile Cn false 33) 22 45 := byJoin cfalse_33_22_33 cfalse_33_33_45
lemma cfalse_33_0_45 : By (tile Cn false 33) 0 45 := byJoin cfalse_33_0_22 cfalse_33_22_45
lemma cfalse_33_45_47 : By (tile Cn false 33) 45 47 := by
  apply byRun (tile Cn false 33) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_33_47_50 : By (tile Cn false 33) 47 50 := by
  apply byRun (tile Cn false 33) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_33_45_50 : By (tile Cn false 33) 45 50 := byJoin cfalse_33_45_47 cfalse_33_47_50
lemma cfalse_33_50_53 : By (tile Cn false 33) 50 53 := by
  apply byRun (tile Cn false 33) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_33_53_56 : By (tile Cn false 33) 53 56 := by
  apply byRun (tile Cn false 33) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_33_50_56 : By (tile Cn false 33) 50 56 := byJoin cfalse_33_50_53 cfalse_33_53_56
lemma cfalse_33_45_56 : By (tile Cn false 33) 45 56 := byJoin cfalse_33_45_50 cfalse_33_50_56
lemma cfalse_33_56_58 : By (tile Cn false 33) 56 58 := by
  apply byRun (tile Cn false 33) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_33_58_61 : By (tile Cn false 33) 58 61 := by
  apply byRun (tile Cn false 33) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_33_56_61 : By (tile Cn false 33) 56 61 := byJoin cfalse_33_56_58 cfalse_33_58_61
lemma cfalse_33_61_64 : By (tile Cn false 33) 61 64 := by
  apply byRun (tile Cn false 33) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_33_64_67 : By (tile Cn false 33) 64 67 := by
  apply byRun (tile Cn false 33) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_33_61_67 : By (tile Cn false 33) 61 67 := byJoin cfalse_33_61_64 cfalse_33_64_67
lemma cfalse_33_56_67 : By (tile Cn false 33) 56 67 := byJoin cfalse_33_56_61 cfalse_33_61_67
lemma cfalse_33_45_67 : By (tile Cn false 33) 45 67 := byJoin cfalse_33_45_56 cfalse_33_56_67
lemma cfalse_33_67_69 : By (tile Cn false 33) 67 69 := by
  apply byRun (tile Cn false 33) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_33_69_72 : By (tile Cn false 33) 69 72 := by
  apply byRun (tile Cn false 33) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_33_67_72 : By (tile Cn false 33) 67 72 := byJoin cfalse_33_67_69 cfalse_33_69_72
lemma cfalse_33_72_75 : By (tile Cn false 33) 72 75 := by
  apply byRun (tile Cn false 33) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_33_75_78 : By (tile Cn false 33) 75 78 := by
  apply byRun (tile Cn false 33) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_33_72_78 : By (tile Cn false 33) 72 78 := byJoin cfalse_33_72_75 cfalse_33_75_78
lemma cfalse_33_67_78 : By (tile Cn false 33) 67 78 := byJoin cfalse_33_67_72 cfalse_33_72_78
lemma cfalse_33_78_81 : By (tile Cn false 33) 78 81 := by
  apply byRun (tile Cn false 33) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_33_81_84 : By (tile Cn false 33) 81 84 := by
  apply byRun (tile Cn false 33) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_33_78_84 : By (tile Cn false 33) 78 84 := byJoin cfalse_33_78_81 cfalse_33_81_84
lemma cfalse_33_84_87 : By (tile Cn false 33) 84 87 := by
  apply byRun (tile Cn false 33) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_33_87_90 : By (tile Cn false 33) 87 90 := by
  apply byRun (tile Cn false 33) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_33_84_90 : By (tile Cn false 33) 84 90 := byJoin cfalse_33_84_87 cfalse_33_87_90
lemma cfalse_33_78_90 : By (tile Cn false 33) 78 90 := byJoin cfalse_33_78_84 cfalse_33_84_90
lemma cfalse_33_67_90 : By (tile Cn false 33) 67 90 := byJoin cfalse_33_67_78 cfalse_33_78_90
lemma cfalse_33_45_90 : By (tile Cn false 33) 45 90 := byJoin cfalse_33_45_67 cfalse_33_67_90
lemma cfalse_33_0_90 : By (tile Cn false 33) 0 90 := byJoin cfalse_33_0_45 cfalse_33_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse34
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_34_0_2 : By (tile Cn false 34) 0 2 := by
  apply byRun (tile Cn false 34) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_34_2_5 : By (tile Cn false 34) 2 5 := by
  apply byRun (tile Cn false 34) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_34_0_5 : By (tile Cn false 34) 0 5 := byJoin cfalse_34_0_2 cfalse_34_2_5
lemma cfalse_34_5_8 : By (tile Cn false 34) 5 8 := by
  apply byRun (tile Cn false 34) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_34_8_11 : By (tile Cn false 34) 8 11 := by
  apply byRun (tile Cn false 34) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_34_5_11 : By (tile Cn false 34) 5 11 := byJoin cfalse_34_5_8 cfalse_34_8_11
lemma cfalse_34_0_11 : By (tile Cn false 34) 0 11 := byJoin cfalse_34_0_5 cfalse_34_5_11
lemma cfalse_34_11_13 : By (tile Cn false 34) 11 13 := by
  apply byRun (tile Cn false 34) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_34_13_16 : By (tile Cn false 34) 13 16 := by
  apply byRun (tile Cn false 34) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_34_11_16 : By (tile Cn false 34) 11 16 := byJoin cfalse_34_11_13 cfalse_34_13_16
lemma cfalse_34_16_19 : By (tile Cn false 34) 16 19 := by
  apply byRun (tile Cn false 34) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_34_19_22 : By (tile Cn false 34) 19 22 := by
  apply byRun (tile Cn false 34) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_34_16_22 : By (tile Cn false 34) 16 22 := byJoin cfalse_34_16_19 cfalse_34_19_22
lemma cfalse_34_11_22 : By (tile Cn false 34) 11 22 := byJoin cfalse_34_11_16 cfalse_34_16_22
lemma cfalse_34_0_22 : By (tile Cn false 34) 0 22 := byJoin cfalse_34_0_11 cfalse_34_11_22
lemma cfalse_34_22_24 : By (tile Cn false 34) 22 24 := by
  apply byRun (tile Cn false 34) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_34_24_27 : By (tile Cn false 34) 24 27 := by
  apply byRun (tile Cn false 34) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_34_22_27 : By (tile Cn false 34) 22 27 := byJoin cfalse_34_22_24 cfalse_34_24_27
lemma cfalse_34_27_30 : By (tile Cn false 34) 27 30 := by
  apply byRun (tile Cn false 34) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_34_30_33 : By (tile Cn false 34) 30 33 := by
  apply byRun (tile Cn false 34) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_34_27_33 : By (tile Cn false 34) 27 33 := byJoin cfalse_34_27_30 cfalse_34_30_33
lemma cfalse_34_22_33 : By (tile Cn false 34) 22 33 := byJoin cfalse_34_22_27 cfalse_34_27_33
lemma cfalse_34_33_36 : By (tile Cn false 34) 33 36 := by
  apply byRun (tile Cn false 34) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_34_36_39 : By (tile Cn false 34) 36 39 := by
  apply byRun (tile Cn false 34) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_34_33_39 : By (tile Cn false 34) 33 39 := byJoin cfalse_34_33_36 cfalse_34_36_39
lemma cfalse_34_39_42 : By (tile Cn false 34) 39 42 := by
  apply byRun (tile Cn false 34) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_34_42_45 : By (tile Cn false 34) 42 45 := by
  apply byRun (tile Cn false 34) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_34_39_45 : By (tile Cn false 34) 39 45 := byJoin cfalse_34_39_42 cfalse_34_42_45
lemma cfalse_34_33_45 : By (tile Cn false 34) 33 45 := byJoin cfalse_34_33_39 cfalse_34_39_45
lemma cfalse_34_22_45 : By (tile Cn false 34) 22 45 := byJoin cfalse_34_22_33 cfalse_34_33_45
lemma cfalse_34_0_45 : By (tile Cn false 34) 0 45 := byJoin cfalse_34_0_22 cfalse_34_22_45
lemma cfalse_34_45_47 : By (tile Cn false 34) 45 47 := by
  apply byRun (tile Cn false 34) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_34_47_50 : By (tile Cn false 34) 47 50 := by
  apply byRun (tile Cn false 34) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_34_45_50 : By (tile Cn false 34) 45 50 := byJoin cfalse_34_45_47 cfalse_34_47_50
lemma cfalse_34_50_53 : By (tile Cn false 34) 50 53 := by
  apply byRun (tile Cn false 34) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_34_53_56 : By (tile Cn false 34) 53 56 := by
  apply byRun (tile Cn false 34) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_34_50_56 : By (tile Cn false 34) 50 56 := byJoin cfalse_34_50_53 cfalse_34_53_56
lemma cfalse_34_45_56 : By (tile Cn false 34) 45 56 := byJoin cfalse_34_45_50 cfalse_34_50_56
lemma cfalse_34_56_58 : By (tile Cn false 34) 56 58 := by
  apply byRun (tile Cn false 34) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_34_58_61 : By (tile Cn false 34) 58 61 := by
  apply byRun (tile Cn false 34) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_34_56_61 : By (tile Cn false 34) 56 61 := byJoin cfalse_34_56_58 cfalse_34_58_61
lemma cfalse_34_61_64 : By (tile Cn false 34) 61 64 := by
  apply byRun (tile Cn false 34) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_34_64_67 : By (tile Cn false 34) 64 67 := by
  apply byRun (tile Cn false 34) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_34_61_67 : By (tile Cn false 34) 61 67 := byJoin cfalse_34_61_64 cfalse_34_64_67
lemma cfalse_34_56_67 : By (tile Cn false 34) 56 67 := byJoin cfalse_34_56_61 cfalse_34_61_67
lemma cfalse_34_45_67 : By (tile Cn false 34) 45 67 := byJoin cfalse_34_45_56 cfalse_34_56_67
lemma cfalse_34_67_69 : By (tile Cn false 34) 67 69 := by
  apply byRun (tile Cn false 34) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_34_69_72 : By (tile Cn false 34) 69 72 := by
  apply byRun (tile Cn false 34) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_34_67_72 : By (tile Cn false 34) 67 72 := byJoin cfalse_34_67_69 cfalse_34_69_72
lemma cfalse_34_72_75 : By (tile Cn false 34) 72 75 := by
  apply byRun (tile Cn false 34) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_34_75_78 : By (tile Cn false 34) 75 78 := by
  apply byRun (tile Cn false 34) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_34_72_78 : By (tile Cn false 34) 72 78 := byJoin cfalse_34_72_75 cfalse_34_75_78
lemma cfalse_34_67_78 : By (tile Cn false 34) 67 78 := byJoin cfalse_34_67_72 cfalse_34_72_78
lemma cfalse_34_78_81 : By (tile Cn false 34) 78 81 := by
  apply byRun (tile Cn false 34) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_34_81_84 : By (tile Cn false 34) 81 84 := by
  apply byRun (tile Cn false 34) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_34_78_84 : By (tile Cn false 34) 78 84 := byJoin cfalse_34_78_81 cfalse_34_81_84
lemma cfalse_34_84_87 : By (tile Cn false 34) 84 87 := by
  apply byRun (tile Cn false 34) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_34_87_90 : By (tile Cn false 34) 87 90 := by
  apply byRun (tile Cn false 34) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_34_84_90 : By (tile Cn false 34) 84 90 := byJoin cfalse_34_84_87 cfalse_34_87_90
lemma cfalse_34_78_90 : By (tile Cn false 34) 78 90 := byJoin cfalse_34_78_84 cfalse_34_84_90
lemma cfalse_34_67_90 : By (tile Cn false 34) 67 90 := byJoin cfalse_34_67_78 cfalse_34_78_90
lemma cfalse_34_45_90 : By (tile Cn false 34) 45 90 := byJoin cfalse_34_45_67 cfalse_34_67_90
lemma cfalse_34_0_90 : By (tile Cn false 34) 0 90 := byJoin cfalse_34_0_45 cfalse_34_45_90
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
lemma gfalse_oai: GoodS Cn false := by
  intro i hi; interval_cases i
  · exact cfalse_0_0_90
  · exact cfalse_1_0_90
  · exact cfalse_2_0_90
  · exact cfalse_3_0_90
  · exact cfalse_4_0_90
  · exact cfalse_5_0_90
  · exact cfalse_6_0_90
  · exact cfalse_7_0_90
  · exact cfalse_8_0_90
  · exact cfalse_9_0_90
  · exact cfalse_10_0_90
  · exact cfalse_11_0_90
  · exact cfalse_12_0_90
  · exact cfalse_13_0_90
  · exact cfalse_14_0_90
  · exact cfalse_15_0_90
  · exact cfalse_16_0_90
  · exact cfalse_17_0_90
  · exact cfalse_18_0_90
  · exact cfalse_19_0_90
  · exact cfalse_20_0_90
  · exact cfalse_21_0_90
  · exact cfalse_22_0_90
  · exact cfalse_23_0_90
  · exact cfalse_24_0_90
  · exact cfalse_25_0_90
  · exact cfalse_26_0_90
  · exact cfalse_27_0_90
  · exact cfalse_28_0_90
  · exact cfalse_29_0_90
  · exact cfalse_30_0_90
  · exact cfalse_31_0_90
  · exact cfalse_32_0_90
  · exact cfalse_33_0_90
  · exact cfalse_34_0_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Mid.Tab.gfalse_oai := @OAI.GeneralMahler.SCal.Mid.Tab.gfalse_oai
