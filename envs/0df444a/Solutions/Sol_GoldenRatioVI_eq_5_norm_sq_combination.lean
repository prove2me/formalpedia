-- Prove2me | solution 1 for GoldenRatioVI.eq_5_norm_sq_combination
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:52:37.109044+00:00
-- url     : https://prove2.me/submissions/b9e328f1-822c-40d7-a323-aa7844217a70

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (α : ℝ) :
    ‖α • a + (1 - α) • b‖ ^ 2 =
      α * ‖a‖ ^ 2 + (1 - α) * ‖b‖ ^ 2 - α * (1 - α) * ‖a - b‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm a b]
  ring
