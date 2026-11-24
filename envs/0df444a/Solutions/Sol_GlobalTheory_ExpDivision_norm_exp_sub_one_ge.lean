-- Prove2me | solution 1 for GlobalTheory.ExpDivision.norm_exp_sub_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:44.854612+00:00
-- url     : https://prove2.me/submissions/da0358e1-20b2-42c1-9a86-253dcee6ac2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution (x : ℝ) :
    4 * |x - round x| ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by
  have h1 : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ)) := by
    have : Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ) + (round x : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 := abs_sub_round x
  set d := x - round x
  have hp := Real.pi_pos
  have e : 2 * Real.pi * d / 2 = Real.pi * d := by ring
  have h3 : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hp]; nlinarith
  have h4 := Real.mul_abs_le_abs_sin h3
  rw [abs_mul, abs_of_pos hp] at h4
  have e2 : 2 / Real.pi * (Real.pi * |d|) = 2 * |d| := by field_simp
  rw [e2] at h4
  rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  linarith
end GlobalTheory.ExpDivision
