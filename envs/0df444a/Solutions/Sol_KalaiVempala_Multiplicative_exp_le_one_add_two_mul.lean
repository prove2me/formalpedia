-- Prove2me | solution 1 for KalaiVempala.Multiplicative.exp_le_one_add_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:03:20.079421+00:00
-- url     : https://prove2.me/submissions/8c102228-230c-4524-96c4-01d5c95e3dcf

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

set_option autoImplicit false
open MeasureTheory OracleRO.ApproxFPL

theorem solution (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A)
    (h : ε ≤ 1 / A) : Real.exp (ε * A) ≤ 1 + 2 * ε * A := by
  have hx0 : 0 ≤ ε * A := by positivity
  have hx1 : ε * A ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h hA.le
    rwa [one_div, inv_mul_cancel₀ hA.ne'] at this
  have h1 := Real.abs_exp_sub_one_sub_id_le (x := ε * A) (by rw [abs_of_nonneg hx0]; exact hx1)
  have h2 := (abs_le.mp h1).2
  nlinarith
