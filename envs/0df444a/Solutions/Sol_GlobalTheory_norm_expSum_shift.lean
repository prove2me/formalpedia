-- Prove2me | solution 1 for GlobalTheory.norm_expSum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:06.0975+00:00
-- url     : https://prove2.me/submissions/07954212-e8c5-49be-ae11-3dac957ec6e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced

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
theorem _root_.solution (s : Finset ℕ) (b : ℕ → ℂ) (c t : ℝ) :
    ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)‖
      = ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ := by
  have : ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)
      = Complex.exp (((-(2 * Real.pi * c * t) : ℝ) : ℂ) * I) *
        ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
end GlobalTheory
