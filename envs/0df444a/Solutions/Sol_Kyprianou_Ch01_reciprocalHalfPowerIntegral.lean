-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalHalfPowerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:13:54.535268+00:00
-- url     : https://prove2.me/submissions/0eb57cb7-00a2-45f9-a88d-08431fa2ed2f

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem solution (g : ℝ → ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      x ^ (-(3 / 2 : ℝ)) * g (x ^ (-(1 / 2 : ℝ))) ∂volume) =
      2 * (∫ y in Set.Ioi (0 : ℝ), g y ∂volume) := by
  have h := integral_comp_rpow_Ioi g
    (p := -(1 / 2 : ℝ)) (by norm_num)
  have heq : (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) := by ring
  have hhalf :
      ((1 / 2 : ℝ)) *
        (∫ x in Set.Ioi (0 : ℝ),
          x ^ (-(3 / 2 : ℝ)) * g (x ^ (-(1 / 2 : ℝ))) ∂volume) =
      ∫ y in Set.Ioi (0 : ℝ), g y ∂volume := by
    rw [← integral_const_mul]
    convert h using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [heq, abs_neg, abs_of_pos (by norm_num : 0 < (1 / 2 : ℝ)),
      smul_eq_mul]
    ring
  linarith [hhalf]
