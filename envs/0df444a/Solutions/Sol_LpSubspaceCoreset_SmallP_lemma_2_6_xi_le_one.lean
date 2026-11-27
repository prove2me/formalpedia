-- Prove2me | solution 1 for LpSubspaceCoreset.SmallP.lemma_2_6_xi_le_one
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:50:02.525879+00:00
-- url     : https://prove2.me/submissions/b697b127-2811-4315-ab64-1f610eea6160

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost

set_option autoImplicit false

open LpSubspaceCoreset
open LpSubspaceCoreset.SmallP

theorem solution (p : ℝ) (k : ℕ) {n d s₀ s₁ : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ)
    (S₀ : Matrix (Fin s₀) (Fin n) ℝ) (S₁ : Matrix (Fin s₁) (Fin s₀) ℝ) (ξ₀ ξ₁ : ℝ)
    (hξ₁ : 0 ≤ ξ₁) (hξ₁' : ξ₁ ≤ 1)
    (h₀ : LpSubspaceCoreset.SmallP.IsStrongCoreset p k ξ₀ A S₀)
    (h₁ : LpSubspaceCoreset.SmallP.IsStrongCoreset p k ξ₁ (S₀ * A) S₁) :
    (∀ F : Submodule ℝ (EuclideanSpace ℝ (Fin d)), LpSubspaceCoreset.SmallP.InFk k F →
      (1 - ξ₀) * (1 - ξ₁) * LpSubspaceCoreset.SmallP.cost p A F ≤
          LpSubspaceCoreset.SmallP.cost p (S₁ * (S₀ * A)) F ∧
        LpSubspaceCoreset.SmallP.cost p (S₁ * (S₀ * A)) F ≤
          (1 + ξ₀) * (1 + ξ₁) * LpSubspaceCoreset.SmallP.cost p A F) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ξ₀ = ε / 3 → ξ₁ = ε / 3 →
      LpSubspaceCoreset.SmallP.IsStrongCoreset p k ε A (S₁ * S₀)) ∧
    LpSubspaceCoreset.SmallP.IsRowSampling (S₁ * S₀) := by
  classical
  have hs : IsRowSampling (S₁ * S₀) := by
    intro i
    obtain ⟨j, hj, hj_unique⟩ := h₁.1 i
    obtain ⟨l, hl, hl_unique⟩ := h₀.1 j
    have product_entry (c : Fin n) : (S₁ * S₀) i c = S₁ i j * S₀ j c := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single j ?_ (by simp)
      intro a _ haj
      have ha : S₁ i a = 0 := by
        by_contra h
        exact haj (hj_unique a h)
      simp [ha]
    refine ⟨l, ?_, ?_⟩
    · change (S₁ * S₀) i l ≠ 0
      rw [product_entry]
      exact mul_ne_zero hj hl
    · intro c hc
      change (S₁ * S₀) i c ≠ 0 at hc
      apply hl_unique c
      intro hz
      exact hc (by rw [product_entry, hz, mul_zero])
  have bounds (F : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hF : InFk k F) :
      (1 - ξ₀) * (1 - ξ₁) * cost p A F ≤ cost p (S₁ * (S₀ * A)) F ∧
        cost p (S₁ * (S₀ * A)) F ≤ (1 + ξ₀) * (1 + ξ₁) * cost p A F := by
    obtain ⟨hl₀, hu₀⟩ := h₀.2 F hF
    obtain ⟨hl₁, hu₁⟩ := h₁.2 F hF
    constructor
    · calc
        _ = (1 - ξ₁) * ((1 - ξ₀) * cost p A F) := by ring
        _ ≤ (1 - ξ₁) * cost p (S₀ * A) F := mul_le_mul_of_nonneg_left hl₀ (sub_nonneg.mpr hξ₁')
        _ ≤ _ := hl₁
    · calc
        _ ≤ (1 + ξ₁) * cost p (S₀ * A) F := hu₁
        _ ≤ (1 + ξ₁) * ((1 + ξ₀) * cost p A F) := mul_le_mul_of_nonneg_left hu₀ (by linarith)
        _ = _ := by ring
  refine ⟨bounds, ?_, hs⟩
  intro ε hε hε' h₀ε h₁ε
  refine ⟨hs, ?_⟩
  intro F hF
  have hcost : 0 ≤ LpSubspaceCoreset.SmallP.cost p A F := by
    unfold LpSubspaceCoreset.SmallP.cost
    exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨hl, hu⟩ := bounds F hF
  rw [h₀ε, h₁ε] at hl hu
  rw [Matrix.mul_assoc]
  exact ⟨(mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ε]) hcost).trans hl,
    hu.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg hε.le (show 0 ≤ 3 - ε by linarith)]) hcost)⟩
