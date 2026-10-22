-- Prove2me | solution 2 for LeviSampling.BaseStock.min_above_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:33:32.458992+00:00
-- url     : https://prove2.me/submissions/7ecdd7f1-8bf2-4e99-ae14-599b93871ba2

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Model
set_option autoImplicit false
open LeviSampling.BaseStock

theorem solution (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (r : ℝ)
    (hr : ∀ y, f r ≤ f y) :
    ConvexOn ℝ Set.univ (minAbove f) ∧
      (∀ x, x ≤ r → minAbove f x = f r) ∧
      (∀ x, r < x → minAbove f x = f x) := by
  have hmono : ∀ u v, r ≤ u → u ≤ v → f u ≤ f v := by
    intro u v hu huv
    have hseg : u ∈ segment ℝ r v := by
      rw [segment_eq_Icc (hu.trans huv)]; exact ⟨hu, huv⟩
    have := hf.le_on_segment (Set.mem_univ r) (Set.mem_univ v) hseg
    exact this.trans (max_le (hr v) le_rfl)
  have hbdd : ∀ x, BddBelow (Set.range fun y : Set.Ici x => f y.1) :=
    fun x => ⟨f r, by rintro _ ⟨y, rfl⟩; show f r ≤ f y.1; exact hr _⟩
  have hle : ∀ x, x ≤ r → minAbove f x = f r := by
    intro x hx
    have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
    unfold minAbove
    apply le_antisymm
    · exact ciInf_le (hbdd x) ⟨r, Set.mem_Ici.2 hx⟩
    · apply le_ciInf
      intro y
      exact hr _
  have hgt : ∀ x, r < x → minAbove f x = f x := by
    intro x hx
    have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
    unfold minAbove
    apply le_antisymm
    · exact ciInf_le (hbdd x) ⟨x, Set.mem_Ici.2 le_rfl⟩
    · apply le_ciInf
      intro y
      exact hmono x _ hx.le y.2
  have hform : minAbove f = fun x => f (max x r) := by
    funext x
    rcases le_or_gt x r with h | h
    · rw [hle x h, max_eq_right h]
    · rw [hgt x h, max_eq_left h.le]
  refine ⟨?_, hle, hgt⟩
  rw [hform]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have e1 := mul_nonneg ha (sub_nonneg.2 (le_max_left x r))
  have e2 := mul_nonneg hb (sub_nonneg.2 (le_max_left y r))
  have e3 := mul_nonneg ha (sub_nonneg.2 (le_max_right x r))
  have e4 := mul_nonneg hb (sub_nonneg.2 (le_max_right y r))
  have h1 : max (a * x + b * y) r ≤ a * max x r + b * max y r := by
    apply max_le
    · linarith
    · have e5 : r = a * r + b * r := by rw [← add_mul, hab, one_mul]
      linarith
  have h2 : r ≤ max (a * x + b * y) r := le_max_right _ _
  calc f (max (a * x + b * y) r) ≤ f (a * max x r + b * max y r) := hmono _ _ h2 h1
    _ ≤ a * f (max x r) + b * f (max y r) := by
        have := hf.2 (Set.mem_univ (max x r)) (Set.mem_univ (max y r)) ha hb hab
        simpa [smul_eq_mul] using this
