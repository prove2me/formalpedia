-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:58.983669+00:00
-- url     : https://prove2.me/submissions/9ed4b159-06bd-4577-8e2e-709515fc1672

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open GlobalTheory.SchwartzIntegralExchange
namespace GlobalTheory.SchwartzIntegralExchange
theorem _root_.solution {S X : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (J : S →ₗ[ℂ] X) (Λ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖Λ w‖ ≤ C * ‖J w‖) :
    ∃ g : X →L[ℂ] ℂ, ∀ w, g (J w) = Λ w := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective J.rangeRestrict
    J.range_rangeRestrict
  have hr' : ∀ y : LinearMap.range J, J (r y) = y := fun y => by
    have := congrArg (fun φ : LinearMap.range J →ₗ[ℂ] LinearMap.range J => (φ y : X)) hr
    simpa using this
  let f : LinearMap.range J →L[ℂ] ℂ := (Λ ∘ₗ r).mkContinuous C (fun y => by
    have := h (r y)
    rw [hr'] at this
    simpa using this)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨g, fun w => ?_⟩
  have h1 := hg ⟨J w, w, rfl⟩
  have h2 := h (r ⟨J w, w, rfl⟩ - w)
  rw [map_sub J, hr'] at h2
  simp only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, map_sub, sub_eq_zero] at h2
  rw [← h2]
  simpa [f] using h1
end GlobalTheory.SchwartzIntegralExchange
