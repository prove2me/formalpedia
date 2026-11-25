-- Prove2me | solution 1 for GlobalTheory.weighted_fejer_positivity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:36.229866+00:00
-- url     : https://prove2.me/submissions/a0f5d8a5-279a-4c74-9dc7-820d709f98b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivity
import Theorems.Thm_GlobalTheory_fejer_re_ge
import Theorems.Thm_GlobalTheory_sum_fejer_weights
import Theorems.Thm_GlobalTheory_weighted_fejer_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  intro J θ
  have n1 : ‖Complex.exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have n2 : ‖Complex.exp (-(θ * I))‖ = 1 := by
    rw [Complex.exp_neg, norm_inv, n1, inv_one]
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [weighted_fejer_split]
    have a := fejer_re_ge w hw J
    have b := fejer_re_ge (w * Complex.exp (θ * I)) (by rw [norm_mul, n1, mul_one]; exact hw) J
    have c := fejer_re_ge (w * Complex.exp (-(θ * I)))
      (by rw [norm_mul, n2, mul_one]; exact hw) J
    linarith
  · rw [weighted_fejer_split]
    have a := fejer_re_ge (Complex.exp (θ * I)) n1.le J
    have b := fejer_re_ge (Complex.exp (θ * I) * Complex.exp (θ * I))
      (by rw [norm_mul, n1, mul_one]) J
    have c : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [c]
    simp only [one_pow, Complex.one_re, mul_one]
    rw [sum_fejer_weights]
    linarith
end GlobalTheory
