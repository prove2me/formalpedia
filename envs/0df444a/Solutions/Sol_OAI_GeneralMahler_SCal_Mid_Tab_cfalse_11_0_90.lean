-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Mid.Tab.cfalse_11_0_90
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:27:45.659612+00:00
-- url     : https://prove2.me/submissions/82c097cc-c754-4f8f-a5e7-7213c0022956

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Rfalse11
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Mid.Tab
open Grid Cert Cert.IV
lemma cfalse_11_0_2 : By (tile Cn false 11) 0 2 := by
  apply byRun (tile Cn false 11) 0 2 2
  · rfl
  decide +kernel
lemma cfalse_11_2_5 : By (tile Cn false 11) 2 5 := by
  apply byRun (tile Cn false 11) 2 3 5
  · rfl
  decide +kernel
lemma cfalse_11_0_5 : By (tile Cn false 11) 0 5 := byJoin cfalse_11_0_2 cfalse_11_2_5
lemma cfalse_11_5_8 : By (tile Cn false 11) 5 8 := by
  apply byRun (tile Cn false 11) 5 3 8
  · rfl
  decide +kernel
lemma cfalse_11_8_11 : By (tile Cn false 11) 8 11 := by
  apply byRun (tile Cn false 11) 8 3 11
  · rfl
  decide +kernel
lemma cfalse_11_5_11 : By (tile Cn false 11) 5 11 := byJoin cfalse_11_5_8 cfalse_11_8_11
lemma cfalse_11_0_11 : By (tile Cn false 11) 0 11 := byJoin cfalse_11_0_5 cfalse_11_5_11
lemma cfalse_11_11_13 : By (tile Cn false 11) 11 13 := by
  apply byRun (tile Cn false 11) 11 2 13
  · rfl
  decide +kernel
lemma cfalse_11_13_16 : By (tile Cn false 11) 13 16 := by
  apply byRun (tile Cn false 11) 13 3 16
  · rfl
  decide +kernel
lemma cfalse_11_11_16 : By (tile Cn false 11) 11 16 := byJoin cfalse_11_11_13 cfalse_11_13_16
lemma cfalse_11_16_19 : By (tile Cn false 11) 16 19 := by
  apply byRun (tile Cn false 11) 16 3 19
  · rfl
  decide +kernel
lemma cfalse_11_19_22 : By (tile Cn false 11) 19 22 := by
  apply byRun (tile Cn false 11) 19 3 22
  · rfl
  decide +kernel
lemma cfalse_11_16_22 : By (tile Cn false 11) 16 22 := byJoin cfalse_11_16_19 cfalse_11_19_22
lemma cfalse_11_11_22 : By (tile Cn false 11) 11 22 := byJoin cfalse_11_11_16 cfalse_11_16_22
lemma cfalse_11_0_22 : By (tile Cn false 11) 0 22 := byJoin cfalse_11_0_11 cfalse_11_11_22
lemma cfalse_11_22_24 : By (tile Cn false 11) 22 24 := by
  apply byRun (tile Cn false 11) 22 2 24
  · rfl
  decide +kernel
lemma cfalse_11_24_27 : By (tile Cn false 11) 24 27 := by
  apply byRun (tile Cn false 11) 24 3 27
  · rfl
  decide +kernel
lemma cfalse_11_22_27 : By (tile Cn false 11) 22 27 := byJoin cfalse_11_22_24 cfalse_11_24_27
lemma cfalse_11_27_30 : By (tile Cn false 11) 27 30 := by
  apply byRun (tile Cn false 11) 27 3 30
  · rfl
  decide +kernel
lemma cfalse_11_30_33 : By (tile Cn false 11) 30 33 := by
  apply byRun (tile Cn false 11) 30 3 33
  · rfl
  decide +kernel
lemma cfalse_11_27_33 : By (tile Cn false 11) 27 33 := byJoin cfalse_11_27_30 cfalse_11_30_33
lemma cfalse_11_22_33 : By (tile Cn false 11) 22 33 := byJoin cfalse_11_22_27 cfalse_11_27_33
lemma cfalse_11_33_36 : By (tile Cn false 11) 33 36 := by
  apply byRun (tile Cn false 11) 33 3 36
  · rfl
  decide +kernel
lemma cfalse_11_36_39 : By (tile Cn false 11) 36 39 := by
  apply byRun (tile Cn false 11) 36 3 39
  · rfl
  decide +kernel
lemma cfalse_11_33_39 : By (tile Cn false 11) 33 39 := byJoin cfalse_11_33_36 cfalse_11_36_39
lemma cfalse_11_39_42 : By (tile Cn false 11) 39 42 := by
  apply byRun (tile Cn false 11) 39 3 42
  · rfl
  decide +kernel
lemma cfalse_11_42_45 : By (tile Cn false 11) 42 45 := by
  apply byRun (tile Cn false 11) 42 3 45
  · rfl
  decide +kernel
lemma cfalse_11_39_45 : By (tile Cn false 11) 39 45 := byJoin cfalse_11_39_42 cfalse_11_42_45
lemma cfalse_11_33_45 : By (tile Cn false 11) 33 45 := byJoin cfalse_11_33_39 cfalse_11_39_45
lemma cfalse_11_22_45 : By (tile Cn false 11) 22 45 := byJoin cfalse_11_22_33 cfalse_11_33_45
lemma cfalse_11_0_45 : By (tile Cn false 11) 0 45 := byJoin cfalse_11_0_22 cfalse_11_22_45
lemma cfalse_11_45_47 : By (tile Cn false 11) 45 47 := by
  apply byRun (tile Cn false 11) 45 2 47
  · rfl
  decide +kernel
lemma cfalse_11_47_50 : By (tile Cn false 11) 47 50 := by
  apply byRun (tile Cn false 11) 47 3 50
  · rfl
  decide +kernel
lemma cfalse_11_45_50 : By (tile Cn false 11) 45 50 := byJoin cfalse_11_45_47 cfalse_11_47_50
lemma cfalse_11_50_53 : By (tile Cn false 11) 50 53 := by
  apply byRun (tile Cn false 11) 50 3 53
  · rfl
  decide +kernel
lemma cfalse_11_53_56 : By (tile Cn false 11) 53 56 := by
  apply byRun (tile Cn false 11) 53 3 56
  · rfl
  decide +kernel
lemma cfalse_11_50_56 : By (tile Cn false 11) 50 56 := byJoin cfalse_11_50_53 cfalse_11_53_56
lemma cfalse_11_45_56 : By (tile Cn false 11) 45 56 := byJoin cfalse_11_45_50 cfalse_11_50_56
lemma cfalse_11_56_58 : By (tile Cn false 11) 56 58 := by
  apply byRun (tile Cn false 11) 56 2 58
  · rfl
  decide +kernel
lemma cfalse_11_58_61 : By (tile Cn false 11) 58 61 := by
  apply byRun (tile Cn false 11) 58 3 61
  · rfl
  decide +kernel
lemma cfalse_11_56_61 : By (tile Cn false 11) 56 61 := byJoin cfalse_11_56_58 cfalse_11_58_61
lemma cfalse_11_61_64 : By (tile Cn false 11) 61 64 := by
  apply byRun (tile Cn false 11) 61 3 64
  · rfl
  decide +kernel
lemma cfalse_11_64_67 : By (tile Cn false 11) 64 67 := by
  apply byRun (tile Cn false 11) 64 3 67
  · rfl
  decide +kernel
lemma cfalse_11_61_67 : By (tile Cn false 11) 61 67 := byJoin cfalse_11_61_64 cfalse_11_64_67
lemma cfalse_11_56_67 : By (tile Cn false 11) 56 67 := byJoin cfalse_11_56_61 cfalse_11_61_67
lemma cfalse_11_45_67 : By (tile Cn false 11) 45 67 := byJoin cfalse_11_45_56 cfalse_11_56_67
lemma cfalse_11_67_69 : By (tile Cn false 11) 67 69 := by
  apply byRun (tile Cn false 11) 67 2 69
  · rfl
  decide +kernel
lemma cfalse_11_69_72 : By (tile Cn false 11) 69 72 := by
  apply byRun (tile Cn false 11) 69 3 72
  · rfl
  decide +kernel
lemma cfalse_11_67_72 : By (tile Cn false 11) 67 72 := byJoin cfalse_11_67_69 cfalse_11_69_72
lemma cfalse_11_72_75 : By (tile Cn false 11) 72 75 := by
  apply byRun (tile Cn false 11) 72 3 75
  · rfl
  decide +kernel
lemma cfalse_11_75_78 : By (tile Cn false 11) 75 78 := by
  apply byRun (tile Cn false 11) 75 3 78
  · rfl
  decide +kernel
lemma cfalse_11_72_78 : By (tile Cn false 11) 72 78 := byJoin cfalse_11_72_75 cfalse_11_75_78
lemma cfalse_11_67_78 : By (tile Cn false 11) 67 78 := byJoin cfalse_11_67_72 cfalse_11_72_78
lemma cfalse_11_78_81 : By (tile Cn false 11) 78 81 := by
  apply byRun (tile Cn false 11) 78 3 81
  · rfl
  decide +kernel
lemma cfalse_11_81_84 : By (tile Cn false 11) 81 84 := by
  apply byRun (tile Cn false 11) 81 3 84
  · rfl
  decide +kernel
lemma cfalse_11_78_84 : By (tile Cn false 11) 78 84 := byJoin cfalse_11_78_81 cfalse_11_81_84
lemma cfalse_11_84_87 : By (tile Cn false 11) 84 87 := by
  apply byRun (tile Cn false 11) 84 3 87
  · rfl
  decide +kernel
lemma cfalse_11_87_90 : By (tile Cn false 11) 87 90 := by
  apply byRun (tile Cn false 11) 87 3 90
  · rfl
  decide +kernel
lemma cfalse_11_84_90 : By (tile Cn false 11) 84 90 := byJoin cfalse_11_84_87 cfalse_11_87_90
lemma cfalse_11_78_90 : By (tile Cn false 11) 78 90 := byJoin cfalse_11_78_84 cfalse_11_84_90
lemma cfalse_11_67_90 : By (tile Cn false 11) 67 90 := byJoin cfalse_11_67_78 cfalse_11_78_90
lemma cfalse_11_45_90 : By (tile Cn false 11) 45 90 := byJoin cfalse_11_45_67 cfalse_11_67_90
lemma cfalse_11_0_90_oai : By (tile Cn false 11) 0 90 := byJoin cfalse_11_0_45 cfalse_11_45_90
end GeneralMahler.SCal.Mid.Tab

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Mid.Tab.cfalse_11_0_90_oai := @OAI.GeneralMahler.SCal.Mid.Tab.cfalse_11_0_90_oai
