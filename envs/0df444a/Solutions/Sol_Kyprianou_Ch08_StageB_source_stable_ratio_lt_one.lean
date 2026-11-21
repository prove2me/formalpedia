-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_stable_ratio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:31:43.765885+00:00
-- url     : https://prove2.me/submissions/d6935e22-b013-4919-a988-a86691a07e11

import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false

theorem solution (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β) :
    0 ≤ q / β ^ α ∧ q / β ^ α < 1 := by
  have hα0 : 0 < α := by linarith
  have hqroot : 0 ≤ q ^ (1 / α) :=
    Real.rpow_nonneg hq.le _
  have hβ0 : 0 < β := lt_of_le_of_lt hqroot hβ
  have hpow := Real.rpow_lt_rpow hqroot hβ hα0
  have hrootpow : (q ^ (1 / α)) ^ α = q := by
    rw [← Real.rpow_mul hq.le]
    have hs : 1 / α * α = (1 : ℝ) := by
      field_simp [ne_of_gt hα0]
    simpa only [hs, Real.rpow_one]
  have hgap : q < β ^ α := by
    simpa only [hrootpow] using hpow
  have hden : 0 < β ^ α := Real.rpow_pos_of_pos hβ0 _
  exact ⟨div_nonneg hq.le hden.le, (div_lt_one hden).2 hgap⟩
