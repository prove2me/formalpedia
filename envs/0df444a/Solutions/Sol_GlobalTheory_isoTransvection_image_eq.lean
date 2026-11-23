-- Prove2me | solution 1 for GlobalTheory.isoTransvection.image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:26.087165+00:00
-- url     : https://prove2.me/submissions/ba95b4b1-3a9a-4adf-8273-93b36a4575cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_apply_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
variable (h)
variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]
namespace GlobalTheory.isoTransvection
theorem _root_.solution {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) :
    isoTransvection h x hx (algebraMap R₀ R b) '' (L : Set M) = L := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact apply_mem h x hx hxL hL b hv
  · intro hw
    refine ⟨isoTransvection h x hx (algebraMap R₀ R (-b)) w, apply_mem h x hx hxL hL _ hw, ?_⟩
    rw [apply_apply, map_neg, add_neg_cancel, zero]; rfl
end GlobalTheory.isoTransvection
