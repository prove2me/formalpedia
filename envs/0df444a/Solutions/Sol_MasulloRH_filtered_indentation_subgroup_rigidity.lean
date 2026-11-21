-- Prove2me | solution 1 for MasulloRH.filtered_indentation_subgroup_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:20:29.494182+00:00
-- url     : https://prove2.me/submissions/f853589d-b426-4053-8c19-5d279badf0a1

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Linarith

open Set

theorem solution {D Γ : Type*} [Group Γ] (H : Subgroup Γ) (w : D → Γ → ℝ)
    (hw : ∀ d h, 0 ≤ w d h)
    (hΓ : ∀ d, HasSum (w d) 1)
    (hH : ∀ d, HasSum (fun h : H => w d h) 1) :
    (∀ d h, h ∉ H → w d h = 0) ∧
    (∀ (d e : D) (x y : Γ), x⁻¹*y ∉ H →
      (∀ h : Γ, w d (h⁻¹*x) * w e (h⁻¹*y) = 0) ∧
      (∑' h : Γ, w d (h⁻¹*x) * w e (h⁻¹*y)) = 0) := by
  have hsupport (d : D) (h : Γ) (hh : h ∉ H) : w d h = 0 := by
    have hparts := (hΓ d).summable.tsum_subtype_add_tsum_subtype_compl (H : Set Γ)
    have hsub : (∑' h : (H : Set Γ), w d h) = 1 := (hH d).tsum_eq
    rw [(hΓ d).tsum_eq, hsub] at hparts
    have hsum := (hΓ d).summable.subtype ((H : Set Γ)ᶜ)
    have hle := hsum.le_tsum ⟨h,hh⟩ (fun i _ => hw d i)
    change w d h ≤ ∑' i : ↥((H : Set Γ)ᶜ), w d i at hle
    have hn := hw d h
    linarith
  refine ⟨hsupport, ?_⟩
  intro d e x y hxy
  have point (h : Γ) : w d (h⁻¹*x) * w e (h⁻¹*y) = 0 := by
    by_cases h1 : h⁻¹*x ∈ H
    · have h2 : h⁻¹*y ∉ H := fun hy => hxy (by simpa [mul_assoc] using H.mul_mem (H.inv_mem h1) hy)
      rw [hsupport _ _ h2, mul_zero]
    · rw [hsupport _ _ h1, zero_mul]
  exact ⟨point, by simp only [point, tsum_zero]⟩

