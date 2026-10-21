-- Prove2me | solution 1 for HighResODE.NAGC.sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:23:34.169109+00:00
-- url     : https://prove2.me/submissions/fcf700c2-bfa6-4031-85f6-f7c5e18a83e5

import Mathlib
set_option autoImplicit false

theorem solution (k : ℕ) (hk : 4 ≤ k) :
    ∑ i ∈ Finset.Ico 3 k,
        (((i : ℝ) + 3) * ((i : ℝ) - 1) - 1 / 3 * ((i : ℝ) + 3) * ((i : ℝ) + 1))
      = (2 * (k : ℝ) ^ 3 - 38 * (k : ℝ) + 60) / 9 ∧
    ((k : ℝ) + 1) ^ 3 / 36 ≤ (2 * (k : ℝ) ^ 3 - 38 * (k : ℝ) + 60) / 9 := by
  have key : ∀ m : ℕ, ∑ i ∈ Finset.Ico 3 (3 + m),
        (((i : ℝ) + 3) * ((i : ℝ) - 1) - 1 / 3 * ((i : ℝ) + 3) * ((i : ℝ) + 1))
      = (2 * ((3 + m : ℕ) : ℝ) ^ 3 - 38 * ((3 + m : ℕ) : ℝ) + 60) / 9 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [show 3 + (m + 1) = (3 + m) + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
      push_cast
      ring
  obtain ⟨m, rfl⟩ : ∃ m, k = 3 + m := ⟨k - 3, by omega⟩
  refine ⟨key m, ?_⟩
  have h4 : (4 : ℝ) ≤ ((3 + m : ℕ) : ℝ) := by exact_mod_cast hk
  generalize ((3 + m : ℕ) : ℝ) = x at h4
  nlinarith [sq_nonneg (x - 4), mul_nonneg (sub_nonneg.2 h4) (sq_nonneg (x - 4)), mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 h4)]
