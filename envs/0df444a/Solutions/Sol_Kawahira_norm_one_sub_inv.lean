-- Prove2me | solution 1 for Kawahira.norm_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:07:41.439715+00:00
-- url     : https://prove2.me/submissions/ebf1f1fc-5bad-488c-a63a-39f81b9d1944

import Mathlib

open Complex

theorem solution (w : ℂ) (hw : w ≠ 0) :
    (‖1 - w⁻¹‖ = 1 ↔ w.re = 1 / 2) ∧
      (‖1 - w⁻¹‖ < 1 ↔ 1 / 2 < w.re) := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hrewrite : 1 - w⁻¹ = (w - 1) / w := by
    field_simp
  rw [hrewrite, norm_div]
  constructor
  · constructor
    · intro h
      have hn : ‖w - 1‖ = ‖w‖ := (div_eq_one_iff_eq hnorm.ne').mp h
      have hs : normSq (w - 1) = normSq w := by
        rw [normSq_eq_norm_sq, normSq_eq_norm_sq, hn]
      rw [normSq_sub] at hs
      norm_num at hs ⊢
      linarith
    · intro hre
      apply (div_eq_one_iff_eq hnorm.ne').mpr
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
        ← normSq_eq_norm_sq, normSq_sub]
      norm_num at hre ⊢
      linarith
  · rw [div_lt_one hnorm]
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
      ← normSq_eq_norm_sq, normSq_sub]
    norm_num
    constructor <;> intro h <;> linarith
