-- Prove2me | solution 2 for LevyFoundations.leanlevy_chat16_exp_exponent_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:58:14.30478+00:00
-- url     : https://prove2.me/submissions/aa6be6ad-8dd2-4ce7-8ada-37c2f39c3e69

import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_zero
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_continuous
import Theorems.Thm_LevyFoundations_leanlevy_chat27_exponent_injective_public
import Theorems.Thm_ProbabilityTheory_leanlevy_chat27_continuous_log_unique_narrow

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- The source triple underlying a wrapper triple. -/
private def chat27_original (T : LevyFoundations.LevyKhintchineTriple) :
    ProbabilityTheory.LevyKhintchineTriple :=
  { drift := T.drift
    gaussianVariance := T.gaussianVariance
    levyMeasure := T.levyMeasure
    levyMeasure_isLevyMeasure := T.levyMeasure_condition }

theorem solution
    (T U : LevyFoundations.LevyKhintchineTriple)
    (h : ∀ ξ : ℝ, Complex.exp (LevyFoundations.exponent T ξ) =
       Complex.exp (LevyFoundations.exponent U ξ)) :
    T = U := by
  have hT : Continuous (LevyFoundations.exponent T) := by
    change Continuous ((chat27_original T).exponent)
    exact ProbabilityTheory.LevyKhintchineTriple.exponent_continuous (chat27_original T)
  have hU : Continuous (LevyFoundations.exponent U) := by
    change Continuous ((chat27_original U).exponent)
    exact ProbabilityTheory.LevyKhintchineTriple.exponent_continuous (chat27_original U)
  have hzero : LevyFoundations.exponent T 0 = LevyFoundations.exponent U 0 := by
    change (chat27_original T).exponent 0 = (chat27_original U).exponent 0
    rw [ProbabilityTheory.LevyKhintchineTriple.exponent_zero,
        ProbabilityTheory.LevyKhintchineTriple.exponent_zero]
  have hlog : LevyFoundations.exponent T = LevyFoundations.exponent U :=
    ProbabilityTheory.leanlevy_chat27_continuous_log_unique_narrow hT hU hzero h
  exact LevyFoundations.leanlevy_chat27_exponent_injective_public T U
    (fun ξ => congrFun hlog ξ)
