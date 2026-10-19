-- Prove2me | solution 1 for GoodmanWitten.strong_cross_section_estimate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:51:13.755053+00:00
-- url     : https://prove2.me/submissions/0995fc98-f61d-4da5-81b2-f44b618eaabb

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution : ∃ C : ℝ, |C / 2.0 - 1| ≤ 0.05 ∧
    ∀ A : ℝ, 0 < A → strongCrossSection A = C * A ^ ((2 : ℝ) / 3) * 1e-25 := by
  refine ⟨4 * Real.pi * 1.25 ^ 2 * 1e-1, ?_, ?_⟩
  · have p1 := Real.pi_gt_d6
    have p2 := Real.pi_lt_d6
    rw [abs_le]; constructor <;> nlinarith
  · intro A hA
    unfold strongCrossSection nuclearRadius
    have h : (A ^ ((1 : ℝ) / 3)) ^ 2 = A ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]; norm_num
    rw [mul_pow, mul_pow, h]
    ring
