-- Prove2me | solution 1 for GlobalTheory.isoTransvection.apply_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:40.288871+00:00
-- url     : https://prove2.me/submissions/fc3b4a94-457f-4c99-950f-139989e4ca28

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
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) (v : M) :
    isoTransvection h x hx (algebraMap R₀ R b) v ∈ L ↔ v ∈ L := by
  refine ⟨fun H => ?_, apply_mem h x hx hxL hL b⟩
  have := apply_mem h x hx hxL hL (-b) H
  rwa [apply_apply, map_neg, neg_add_cancel, zero] at this
end GlobalTheory.isoTransvection
