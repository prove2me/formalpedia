-- Prove2me | solution 1 for Kyprianou.Ch01.geometricMarkCompoundPoissonExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:56:56.866417+00:00
-- url     : https://prove2.me/submissions/90f3ff38-a7fd-4471-a471-17feaa571e19

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpCompoundPoissonExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

/-! Logarithmic-jump CP exponent represents a geometric number of arbitrary marks. -/
theorem solution
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Complex.exp (∑' n : ℕ,
      ((q : ℂ) ^ (n + 1) / ((n : ℂ) + 1)) *
        (z ^ (n + 1) - 1)) =
      (((1 - q : ℝ) : ℂ) / (1 - (q : ℂ) * z)) := by
  have hqn : ‖(q : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_pos hq0] using hq1
  have hqnz : ‖(q : ℂ) * z‖ < 1 := by
    calc
      ‖(q : ℂ) * z‖ = ‖(q : ℂ)‖ * ‖z‖ := norm_mul _ _
      _ ≤ ‖(q : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < 1 := by simpa using hqn
  have hbase := Kyprianou.Ch01.logarithmicJumpCompoundPoissonExponent
    (q : ℂ) z hqn hqnz
  calc
    Complex.exp (∑' n : ℕ,
      ((q : ℂ) ^ (n + 1) / ((n : ℂ) + 1)) *
        (z ^ (n + 1) - 1)) =
      Complex.exp (∑' n : ℕ,
        (((q : ℂ) * z) ^ (n + 1) / ((n : ℂ) + 1) -
          (q : ℂ) ^ (n + 1) / ((n : ℂ) + 1))) := by
        congr 1
        apply tsum_congr
        intro n
        rw [mul_pow]
        ring
    _ = (1 - (q : ℂ)) / (1 - (q : ℂ) * z) := hbase
    _ = (((1 - q : ℝ) : ℂ) / (1 - (q : ℂ) * z)) := by
      push_cast
      ring
