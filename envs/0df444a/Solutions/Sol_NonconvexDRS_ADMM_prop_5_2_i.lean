-- Prove2me | solution 1 for NonconvexDRS.ADMM.prop_5_2_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:47:03.683247+00:00
-- url     : https://prove2.me/submissions/90359b27-7ed9-4745-a8a8-f670fb322b80

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting
set_option autoImplicit false
open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace
open NonconvexDRS.ADMM

theorem solution {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (β : ℝ) (hβ : 0 < β) (hh : NonconvexDRS.Tight.IsProper h)
    (hX : ∀ s, (Xbeta h C β s).Nonempty) :
    NonconvexDRS.Tight.IsProper (imageFn C h) := by
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨xβ, hxβ⟩ := hX s
    have hle : h xβ ≤ imageFn C h s := by
      unfold imageFn
      apply le_iInf₂
      intro x hx
      have h1 := hxβ x
      rw [hx] at h1
      have h0 : (0 : EReal) ≤ ((β / 2 * ‖C xβ - s‖ ^ 2 : ℝ) : EReal) := by
        rw [EReal.coe_nonneg]; positivity
      have h2 : h xβ ≤ h xβ + ((β / 2 * ‖C xβ - s‖ ^ 2 : ℝ) : EReal) := le_add_of_nonneg_right h0
      refine h2.trans (h1.trans ?_)
      simp
    exact ne_bot_of_le_ne_bot (hh.1 xβ) hle
  · obtain ⟨x0, hx0⟩ := hh.2
    refine ⟨C x0, ?_⟩
    have : imageFn C h (C x0) ≤ h x0 := by
      unfold imageFn
      exact iInf₂_le (f := fun x (_ : C x = C x0) => h x) x0 rfl
    exact ne_top_of_le_ne_top hx0 this
