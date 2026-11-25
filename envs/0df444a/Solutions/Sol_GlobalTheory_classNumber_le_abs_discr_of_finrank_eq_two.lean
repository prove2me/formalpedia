-- Prove2me | solution 1 for GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:25.316344+00:00
-- url     : https://prove2.me/submissions/56671beb-1875-4c3b-b9a9-68c22cd5baa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ClassNumberLeAbsDiscrOfFinrankEqTwo
import Theorems.Thm_GlobalTheory_classNumber_le_sqrt_discr_mul_pow_pred
import Theorems.Thm_GlobalTheory_one_le_sqrt_abs_discr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    (NumberField.classNumber K : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
  have hb := _root_.GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  rw [h] at hb
  norm_num at hb
  have hs := _root_.GlobalTheory.one_le_sqrt_abs_discr K
  set s := √|(NumberField.discr K : ℝ)| with hs_def
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hsq : s * s = |(NumberField.discr K : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  calc (NumberField.classNumber K : ℝ) ≤ s * (1 + Real.log s) := hb
    _ ≤ s * s := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    _ = |(NumberField.discr K : ℝ)| := hsq
end _root_.GlobalTheory
end GlobalTheory
