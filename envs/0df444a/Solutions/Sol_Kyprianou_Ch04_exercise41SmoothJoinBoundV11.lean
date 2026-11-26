-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SmoothJoinBoundV11
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:46:31.939564+00:00
-- url     : https://prove2.me/submissions/00b7b3de-0cbe-44aa-ab4f-9edb6c27a529

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℕ → ℝ → ℝ)
    (hP : ∀ n x, 0 ≤ p n x ∧ p n x ≤ max 0 x)
    (hD : ∀ n x, 0 ≤ deriv (p n) x ∧ deriv (p n) x ≤ 1)
    (R : ℝ) (hRpos : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n x, |x| ≤ R →
      ‖deriv fLeft (-p n (-x)) * deriv (p n) (-x) +
        deriv fRight (p n x) * deriv (p n) x‖ ≤ K := by
  obtain ⟨A,hA⟩ := (isCompact_Icc (a := -R) (b := R)).bddAbove_image
    hL.continuous_deriv_one.norm.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := -R) (b := R)).bddAbove_image
    hR.continuous_deriv_one.norm.continuousOn
  refine ⟨max 0 A + max 0 B, add_nonneg (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro n x hx
  have hm := abs_le.mp hx
  have h1 := hP n (-x)
  have h2 := hP n x
  have h1' : -p n (-x) ∈ Icc (-R) R := by
    have hu := h1.2.trans (max_le hRpos.le (by linarith [hm.1]))
    exact ⟨by linarith,by linarith [h1.1]⟩
  have h2' : p n x ∈ Icc (-R) R := by
    exact ⟨by linarith [h2.1], h2.2.trans (max_le hRpos.le hm.2)⟩
  have hla : ‖deriv fLeft (-p n (-x))‖ ≤ max 0 A :=
    (hA ⟨_,h1',rfl⟩).trans (le_max_right _ _)
  have hrb : ‖deriv fRight (p n x)‖ ≤ max 0 B :=
    (hB ⟨_,h2',rfl⟩).trans (le_max_right _ _)
  have hd (y : ℝ) : ‖deriv (p n) y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hD n y).1]
    exact (hD n y).2
  calc
    _ ≤ ‖deriv fLeft (-p n (-x)) * deriv (p n) (-x)‖ +
        ‖deriv fRight (p n x) * deriv (p n) x‖ := norm_add_le _ _
    _ ≤ max 0 A + max 0 B := by
      rw [norm_mul, norm_mul]
      exact add_le_add
        (by simpa using mul_le_mul hla (hd (-x)) (norm_nonneg _) (le_max_left _ _))
        (by simpa using mul_le_mul hrb (hd x) (norm_nonneg _) (le_max_left _ _))
