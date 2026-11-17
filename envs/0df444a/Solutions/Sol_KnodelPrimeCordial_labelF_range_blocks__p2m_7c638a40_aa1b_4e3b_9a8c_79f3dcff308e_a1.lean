-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_range_blocks__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:06:58.928592+00:00
-- url     : https://prove2.me/submissions/1de9df80-6456-4ecd-abe3-1fb574a8c088

import Mathlib

theorem solution (q y : ℕ) (hy : y ∈ Set.Icc 1 (12 * q)) :
    ∃ k t : ℕ, k < q ∧ t ∈ Set.Icc 1 12 ∧ y = 12 * k + t := by
  rcases Set.mem_Icc.mp hy with ⟨hy₁, hy₂⟩
  refine ⟨(y - 1) / 12, (y - 1) % 12 + 1, ?_, ?_, ?_⟩
  · apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 12)).2
    omega
  · constructor
    · omega
    · have hmod := Nat.mod_lt (y - 1) (by omega : 0 < 12)
      omega
  · have hdiv := Nat.mod_add_div (y - 1) 12
    omega
