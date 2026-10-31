-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Mid.Tab.ctrue_4_0_90
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:55:57.517863+00:00
-- url     : https://prove2.me/submissions/44f923e0-69af-4dc0-ae39-d462818c750e

import Mathlib
import Definitions.Def_OAIQ026G002

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rtrue4
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma ctrue_4_0_2 : By (tile Cn true 4) 0 2 := by
  apply byRun (tile Cn true 4) 0 2 2
  · rfl
  decide +kernel
lemma ctrue_4_2_5 : By (tile Cn true 4) 2 5 := by
  apply byRun (tile Cn true 4) 2 3 5
  · rfl
  decide +kernel
lemma ctrue_4_0_5 : By (tile Cn true 4) 0 5 := byJoin ctrue_4_0_2 ctrue_4_2_5
lemma ctrue_4_5_8 : By (tile Cn true 4) 5 8 := by
  apply byRun (tile Cn true 4) 5 3 8
  · rfl
  decide +kernel
lemma ctrue_4_8_11 : By (tile Cn true 4) 8 11 := by
  apply byRun (tile Cn true 4) 8 3 11
  · rfl
  decide +kernel
lemma ctrue_4_5_11 : By (tile Cn true 4) 5 11 := byJoin ctrue_4_5_8 ctrue_4_8_11
lemma ctrue_4_0_11 : By (tile Cn true 4) 0 11 := byJoin ctrue_4_0_5 ctrue_4_5_11
lemma ctrue_4_11_13 : By (tile Cn true 4) 11 13 := by
  apply byRun (tile Cn true 4) 11 2 13
  · rfl
  decide +kernel
lemma ctrue_4_13_16 : By (tile Cn true 4) 13 16 := by
  apply byRun (tile Cn true 4) 13 3 16
  · rfl
  decide +kernel
lemma ctrue_4_11_16 : By (tile Cn true 4) 11 16 := byJoin ctrue_4_11_13 ctrue_4_13_16
lemma ctrue_4_16_19 : By (tile Cn true 4) 16 19 := by
  apply byRun (tile Cn true 4) 16 3 19
  · rfl
  decide +kernel
lemma ctrue_4_19_22 : By (tile Cn true 4) 19 22 := by
  apply byRun (tile Cn true 4) 19 3 22
  · rfl
  decide +kernel
lemma ctrue_4_16_22 : By (tile Cn true 4) 16 22 := byJoin ctrue_4_16_19 ctrue_4_19_22
lemma ctrue_4_11_22 : By (tile Cn true 4) 11 22 := byJoin ctrue_4_11_16 ctrue_4_16_22
lemma ctrue_4_0_22 : By (tile Cn true 4) 0 22 := byJoin ctrue_4_0_11 ctrue_4_11_22
lemma ctrue_4_22_24 : By (tile Cn true 4) 22 24 := by
  apply byRun (tile Cn true 4) 22 2 24
  · rfl
  decide +kernel
lemma ctrue_4_24_27 : By (tile Cn true 4) 24 27 := by
  apply byRun (tile Cn true 4) 24 3 27
  · rfl
  decide +kernel
lemma ctrue_4_22_27 : By (tile Cn true 4) 22 27 := byJoin ctrue_4_22_24 ctrue_4_24_27
lemma ctrue_4_27_30 : By (tile Cn true 4) 27 30 := by
  apply byRun (tile Cn true 4) 27 3 30
  · rfl
  decide +kernel
lemma ctrue_4_30_33 : By (tile Cn true 4) 30 33 := by
  apply byRun (tile Cn true 4) 30 3 33
  · rfl
  decide +kernel
lemma ctrue_4_27_33 : By (tile Cn true 4) 27 33 := byJoin ctrue_4_27_30 ctrue_4_30_33
lemma ctrue_4_22_33 : By (tile Cn true 4) 22 33 := byJoin ctrue_4_22_27 ctrue_4_27_33
lemma ctrue_4_33_36 : By (tile Cn true 4) 33 36 := by
  apply byRun (tile Cn true 4) 33 3 36
  · rfl
  decide +kernel
lemma ctrue_4_36_39 : By (tile Cn true 4) 36 39 := by
  apply byRun (tile Cn true 4) 36 3 39
  · rfl
  decide +kernel
lemma ctrue_4_33_39 : By (tile Cn true 4) 33 39 := byJoin ctrue_4_33_36 ctrue_4_36_39
lemma ctrue_4_39_42 : By (tile Cn true 4) 39 42 := by
  apply byRun (tile Cn true 4) 39 3 42
  · rfl
  decide +kernel
lemma ctrue_4_42_45 : By (tile Cn true 4) 42 45 := by
  apply byRun (tile Cn true 4) 42 3 45
  · rfl
  decide +kernel
lemma ctrue_4_39_45 : By (tile Cn true 4) 39 45 := byJoin ctrue_4_39_42 ctrue_4_42_45
lemma ctrue_4_33_45 : By (tile Cn true 4) 33 45 := byJoin ctrue_4_33_39 ctrue_4_39_45
lemma ctrue_4_22_45 : By (tile Cn true 4) 22 45 := byJoin ctrue_4_22_33 ctrue_4_33_45
lemma ctrue_4_0_45 : By (tile Cn true 4) 0 45 := byJoin ctrue_4_0_22 ctrue_4_22_45
lemma ctrue_4_45_47 : By (tile Cn true 4) 45 47 := by
  apply byRun (tile Cn true 4) 45 2 47
  · rfl
  decide +kernel
lemma ctrue_4_47_50 : By (tile Cn true 4) 47 50 := by
  apply byRun (tile Cn true 4) 47 3 50
  · rfl
  decide +kernel
lemma ctrue_4_45_50 : By (tile Cn true 4) 45 50 := byJoin ctrue_4_45_47 ctrue_4_47_50
lemma ctrue_4_50_53 : By (tile Cn true 4) 50 53 := by
  apply byRun (tile Cn true 4) 50 3 53
  · rfl
  decide +kernel
lemma ctrue_4_53_56 : By (tile Cn true 4) 53 56 := by
  apply byRun (tile Cn true 4) 53 3 56
  · rfl
  decide +kernel
lemma ctrue_4_50_56 : By (tile Cn true 4) 50 56 := byJoin ctrue_4_50_53 ctrue_4_53_56
lemma ctrue_4_45_56 : By (tile Cn true 4) 45 56 := byJoin ctrue_4_45_50 ctrue_4_50_56
lemma ctrue_4_56_58 : By (tile Cn true 4) 56 58 := by
  apply byRun (tile Cn true 4) 56 2 58
  · rfl
  decide +kernel
lemma ctrue_4_58_61 : By (tile Cn true 4) 58 61 := by
  apply byRun (tile Cn true 4) 58 3 61
  · rfl
  decide +kernel
lemma ctrue_4_56_61 : By (tile Cn true 4) 56 61 := byJoin ctrue_4_56_58 ctrue_4_58_61
lemma ctrue_4_61_64 : By (tile Cn true 4) 61 64 := by
  apply byRun (tile Cn true 4) 61 3 64
  · rfl
  decide +kernel
lemma ctrue_4_64_67 : By (tile Cn true 4) 64 67 := by
  apply byRun (tile Cn true 4) 64 3 67
  · rfl
  decide +kernel
lemma ctrue_4_61_67 : By (tile Cn true 4) 61 67 := byJoin ctrue_4_61_64 ctrue_4_64_67
lemma ctrue_4_56_67 : By (tile Cn true 4) 56 67 := byJoin ctrue_4_56_61 ctrue_4_61_67
lemma ctrue_4_45_67 : By (tile Cn true 4) 45 67 := byJoin ctrue_4_45_56 ctrue_4_56_67
lemma ctrue_4_67_69 : By (tile Cn true 4) 67 69 := by
  apply byRun (tile Cn true 4) 67 2 69
  · rfl
  decide +kernel
lemma ctrue_4_69_72 : By (tile Cn true 4) 69 72 := by
  apply byRun (tile Cn true 4) 69 3 72
  · rfl
  decide +kernel
lemma ctrue_4_67_72 : By (tile Cn true 4) 67 72 := byJoin ctrue_4_67_69 ctrue_4_69_72
lemma ctrue_4_72_75 : By (tile Cn true 4) 72 75 := by
  apply byRun (tile Cn true 4) 72 3 75
  · rfl
  decide +kernel
lemma ctrue_4_75_78 : By (tile Cn true 4) 75 78 := by
  apply byRun (tile Cn true 4) 75 3 78
  · rfl
  decide +kernel
lemma ctrue_4_72_78 : By (tile Cn true 4) 72 78 := byJoin ctrue_4_72_75 ctrue_4_75_78
lemma ctrue_4_67_78 : By (tile Cn true 4) 67 78 := byJoin ctrue_4_67_72 ctrue_4_72_78
lemma ctrue_4_78_81 : By (tile Cn true 4) 78 81 := by
  apply byRun (tile Cn true 4) 78 3 81
  · rfl
  decide +kernel
lemma ctrue_4_81_84 : By (tile Cn true 4) 81 84 := by
  apply byRun (tile Cn true 4) 81 3 84
  · rfl
  decide +kernel
lemma ctrue_4_78_84 : By (tile Cn true 4) 78 84 := byJoin ctrue_4_78_81 ctrue_4_81_84
lemma ctrue_4_84_87 : By (tile Cn true 4) 84 87 := by
  apply byRun (tile Cn true 4) 84 3 87
  · rfl
  decide +kernel
lemma ctrue_4_87_90 : By (tile Cn true 4) 87 90 := by
  apply byRun (tile Cn true 4) 87 3 90
  · rfl
  decide +kernel
lemma ctrue_4_84_90 : By (tile Cn true 4) 84 90 := byJoin ctrue_4_84_87 ctrue_4_87_90
lemma ctrue_4_78_90 : By (tile Cn true 4) 78 90 := byJoin ctrue_4_78_84 ctrue_4_84_90
lemma ctrue_4_67_90 : By (tile Cn true 4) 67 90 := byJoin ctrue_4_67_78 ctrue_4_78_90
lemma ctrue_4_45_90 : By (tile Cn true 4) 45 90 := byJoin ctrue_4_45_67 ctrue_4_67_90
lemma ctrue_4_0_90_oai : By (tile Cn true 4) 0 90 := byJoin ctrue_4_0_45 ctrue_4_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Mid.Tab.ctrue_4_0_90_oai := @OAI.GeneralMahler.SCal.Mid.Tab.ctrue_4_0_90_oai
