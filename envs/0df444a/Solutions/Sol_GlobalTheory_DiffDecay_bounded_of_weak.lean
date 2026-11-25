-- Prove2me | solution 1 for GlobalTheory.DiffDecay.bounded_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:39.336349+00:00
-- url     : https://prove2.me/submissions/98330207-f131-4269-90ce-6a131a382dcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.DiffDecay
variable {E : Type} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.DiffDecay
theorem _root_.solution [TopologicalSpace E] [IsTopologicalAddGroup E] {T : Type} (f : T → E)
    (h : ∀ l : E →L[ℂ] ℂ, ∃ C : ℝ, ∀ t, ‖l (f t)‖ ≤ C) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ, ∀ t, p (f t) ≤ C := by
  let j₀ : E →ₗ[ℂ] WithSemi p := LinearMap.id
  have hj : Continuous j₀ := by
    refine continuous_of_continuousAt_zero j₀ ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hp.tendsto 0
    rw [map_zero] at this
    exact this
  let j : E →L[ℂ] WithSemi p := ⟨j₀, hj⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t => NormedSpace.inclusionInDoubleDual ℂ (WithSemi p) (j (f t)))
    (fun φ => h (φ.comp j))
  refine ⟨C, fun t => ?_⟩
  have := hC t
  rw [show NormedSpace.inclusionInDoubleDual ℂ (WithSemi p) (j (f t)) =
    NormedSpace.inclusionInDoubleDualLi ℂ (j (f t)) from rfl, LinearIsometry.norm_map] at this
  exact this
end GlobalTheory.DiffDecay
