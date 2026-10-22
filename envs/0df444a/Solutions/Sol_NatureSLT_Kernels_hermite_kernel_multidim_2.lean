-- Prove2me | solution 2 for NatureSLT.Kernels.hermite_kernel_multidim
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-21T16:30:36.085284+00:00
-- url     : https://prove2.me/submissions/bf4a394c-194f-4957-8b03-d91aa86b4d0e

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (x y : EuclideanSpace ℝ (Fin n)),
    ∏ i : Fin n, (1 / Real.sqrt (Real.pi * (1 - q ^ 2)) *
        Real.exp (2 * x i * y i * q / (1 + q) - (x i - y i) ^ 2 * q ^ 2 / (1 - q ^ 2))) =
      1 / (1 - q ^ 2) ^ ((n : ℝ) / 2) *
        Real.exp (2 * inner ℝ x y * q / (1 + q) - ‖x - y‖ ^ 2 * q ^ 2 / (1 - q ^ 2))) := by
  intro h
  have := h 1 0 le_rfl zero_lt_one 0 0
  simp at this
  linarith [Real.pi_gt_three]
