-- Prove2me | solution 1 for GlobalTheory.integral_norm_sq_expSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:24.898123+00:00
-- url     : https://prove2.me/submissions/e15f20d9-3e28-49d8-a0b9-d8a8894e85a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Theorems.Thm_GlobalTheory_integral_exp_two_pi_sub

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
namespace GlobalTheory
theorem _root_.solution (s : Finset ℕ) (b : ℕ → ℂ) (y : ℝ) :
    ∫ t in y..(y + 1), ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2
      = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have key : ∀ t : ℝ, ((‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, b n * (starRingEnd ℂ) (b m) *
        Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, conj_ofReal, conj_I, map_natCast, map_ofNat]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_sub]
  simp [hn, Complex.mul_conj']
end GlobalTheory
