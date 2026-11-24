-- Prove2me | solution 1 for GlobalTheory.integral_exp_two_pi_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:19.734252+00:00
-- url     : https://prove2.me/submissions/ff8d97e8-b1dd-4bd8-9edf-5440f91421fe

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
theorem _root_.solution (n m : ℕ) (y : ℝ) :
    ∫ t in y..(y + 1), Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (2 * Real.pi * I * ((n : ℂ) - m)) ≠ 0 := by
      have : (n : ℂ) - m ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, hpi, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ)) := by
      have h1 := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [show 2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ)
        = 2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ) + (((n : ℤ) - m : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, h1, mul_one]
    rw [this]; simp
end GlobalTheory
