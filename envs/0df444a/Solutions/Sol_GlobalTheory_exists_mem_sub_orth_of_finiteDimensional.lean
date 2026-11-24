-- Prove2me | solution 1 for GlobalTheory.exists_mem_sub_orth_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:47.72468+00:00
-- url     : https://prove2.me/submissions/b78847d0-d62a-405f-b21c-9018afe03041

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AbstractCompleteReducibility

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [AddCommGroup E] [Module ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (T : Submodule ℂ E) [FiniteDimensional ℂ T]
    (hT : ∀ t ∈ T, b t t = 0 → t = 0) (ψ : E) : ∃ s ∈ T, ∀ t ∈ T, b t (ψ - s) = 0 := by
  let bs := Module.finBasis ℂ T
  let F : E →ₗ[ℂ] (Fin (finrank ℂ T) → ℂ) := LinearMap.pi fun i => b (bs i : E)
  have key : ∀ x, F x = 0 → ∀ t ∈ T, b t x = 0 := by
    intro x hx t ht
    have h1 : (b.flip x) ∘ₛₗ T.subtype = 0 :=
      bs.ext fun i => by simpa [F] using congrFun hx i
    exact LinearMap.congr_fun h1 ⟨t, ht⟩
  have hinj : Function.Injective (F ∘ₗ T.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext (hT z z.2 (key z hz z z.2))
  have hsurj : Function.Surjective (F ∘ₗ T.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨z, hz⟩ := hsurj (F ψ)
  refine ⟨z, z.2, key (ψ - z) ?_⟩
  rw [map_sub, ← hz]
  simp
end GlobalTheory
