-- Prove2me | solution 1 for NewtonGravitation.shell_angular_zero_radius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:33:38.254463+00:00
-- url     : https://prove2.me/submissions/c5650172-495c-4672-a274-f2c5f9444aee

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem solution (R : ℝ) (hR : 0 < R) :
    (∫ t in (-1 : ℝ)..1,
      R / (2 * (Real.sqrt (R ^ 2)) ^ 3)) = 1 / R ^ 2 := by
  rw [Real.sqrt_sq hR.le, intervalIntegral.integral_const]
  simp only [sub_neg_eq_add, smul_eq_mul]
  field_simp
  ring
