-- Prove2me | solution 1 for GlobalTheory.expSum_sub_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:48:43.255899+00:00
-- url     : https://prove2.me/submissions/ccf5603d-75a0-4c8b-9151-b2a70456e98c

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
theorem _root_.solution (s : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) (k : ℤ) :
    ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * ((x - k : ℝ) : ℂ))
      = ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * x) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := Complex.exp_int_mul_two_pi_mul_I (-(n * k))
  rw [show 2 * Real.pi * I * (n : ℂ) * ((x - k : ℝ) : ℂ)
    = 2 * Real.pi * I * n * x + ((-(n * k) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, h1, mul_one]
end GlobalTheory
