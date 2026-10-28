-- Prove2me | solution 1 for NonconvexDRS.ImageSmooth.prop_5_2_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:19:06.553253+00:00
-- url     : https://prove2.me/submissions/d0e83067-e09a-40be-81ed-d7e13863a924

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

open NonconvexDRS.ImageSmooth in
theorem solution {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) (hh : NonconvexDRS.DRS.IsProper h)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (β : ℝ) (hβ : 0 < β)
    (hX : ∀ s : EuclideanSpace ℝ (Fin p), ∃ xβ : EuclideanSpace ℝ (Fin n), ∀ x,
      h xβ + ((β / 2 * ‖C xβ - s‖ ^ 2 : ℝ) : EReal) ≤ h x + ((β / 2 * ‖C x - s‖ ^ 2 : ℝ) : EReal)) :
    NonconvexDRS.DRS.IsProper (imageFn C h) := by
  obtain ⟨hbot, x0, hx0⟩ := hh
  constructor
  · intro s
    obtain ⟨xβ, hxβ⟩ := hX s
    have hlow : h xβ + ((β / 2 * ‖C xβ - s‖ ^ 2 : ℝ) : EReal) ≤ imageFn C h s := by
      unfold imageFn
      apply le_iInf₂
      intro x hx
      have := hxβ x
      rw [hx, sub_self, norm_zero] at this
      simpa using this
    have hne : h xβ + ((β / 2 * ‖C xβ - s‖ ^ 2 : ℝ) : EReal) ≠ ⊥ :=
      EReal.add_ne_bot_iff.mpr ⟨hbot xβ, EReal.coe_ne_bot _⟩
    intro hb
    rw [hb, le_bot_iff] at hlow
    exact hne hlow
  · refine ⟨C x0, ?_⟩
    have : imageFn C h (C x0) ≤ h x0 := by
      unfold imageFn
      exact iInf_le_of_le x0 (iInf_le_of_le rfl le_rfl)
    intro ht
    rw [ht, top_le_iff] at this
    exact hx0 this
