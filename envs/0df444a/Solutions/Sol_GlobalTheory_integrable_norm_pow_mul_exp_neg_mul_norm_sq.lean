-- Prove2me | solution 1 for GlobalTheory.integrable_norm_pow_mul_exp_neg_mul_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:52.954155+00:00
-- url     : https://prove2.me/submissions/2e896232-94e1-4bab-b784-e051b6a1b5a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped Nat ComplexConjugate
open GlobalTheory
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {E}
namespace GlobalTheory
theorem _root_.solution (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => ‖z‖ ^ n * exp (-b * ‖z‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with h | h
  · exact Integrable.of_finite
  rw [integrable_fun_norm_addHaar volume (f := fun r => r ^ n * exp (-b * r ^ 2))]
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb
    (s := ((Module.finrank ℝ E - 1 + n : ℕ) : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [rpow_natCast, smul_eq_mul, pow_add, mul_assoc]
end GlobalTheory
