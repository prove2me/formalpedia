-- Prove2me | solution 1 for GlobalTheory.T.exists_kernels_eval_zero_eq_sum_integral_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:43.134879+00:00
-- url     : https://prove2.me/submissions/1f0f172e-dba8-4c94-b375-09b76d051326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Theorems.Thm_GlobalTheory_value_at_zero_eq_sum_integral_kernel_iteratedDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ ε : ℝ, 0 < ε → ∃ κ : Fin 3 → ℝ → ℂ, (∀ n, Continuous (κ n) ∧ tsupport (κ n) ⊆ Set.Icc (-ε) ε) ∧ ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → u 0 = ∑ n : Fin 3, ∫ t, κ n t * iteratedDeriv n u t := by
  first | exact @GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv | exact GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv | (intros; apply GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv <;> assumption)
end _root_.GlobalTheory.T
