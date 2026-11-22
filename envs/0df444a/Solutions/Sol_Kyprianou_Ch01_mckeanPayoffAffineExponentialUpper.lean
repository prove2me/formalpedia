-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanPayoffAffineExponentialUpper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:47:35.351937+00:00
-- url     : https://prove2.me/submissions/dd05fb37-48e3-429c-a8cb-59c95ce47d9f

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_Kyprianou_Ch01_mckeanWeightedExponentialTangent
open Real
set_option autoImplicit false

/-- The exponential tangent dominates the put exercise reward globally. -/
theorem solution
    (K phi u z : ℝ) (hphi : 0 < phi) :
    K - Real.exp z ≤
      (K - (1 + 1 / phi) * Real.exp u) +
        (Real.exp u / phi) * Real.exp (-phi * (z - u)) := by
  have hW :=
    Kyprianou.Ch01.mckeanWeightedExponentialTangent
      phi (z - u) hphi
  have hScale : 0 ≤ Real.exp u / phi :=
    div_nonneg (Real.exp_nonneg _) hphi.le
  have hScaled :=
    mul_le_mul_of_nonneg_left hW hScale
  have hCancel : (Real.exp u / phi) * phi = Real.exp u := by
    field_simp
  have hExp : Real.exp u * Real.exp (z - u) = Real.exp z := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEq1 : (1 + 1 / phi) * Real.exp u =
      (Real.exp u / phi) * (1 + phi) := by
    field_simp
    ring
  have hEq2 : (Real.exp u / phi) *
      (phi * Real.exp (z - u) + Real.exp (-phi * (z - u))) =
      Real.exp z + (Real.exp u / phi) *
        Real.exp (-phi * (z - u)) := by
    calc
      _ = (Real.exp u / phi) * phi * Real.exp (z - u) +
          (Real.exp u / phi) * Real.exp (-phi * (z - u)) := by ring
      _ = Real.exp z + (Real.exp u / phi) *
          Real.exp (-phi * (z - u)) := by rw [hCancel, hExp]
  rw [← hEq1, hEq2] at hScaled
  linarith
