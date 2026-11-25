-- Prove2me | solution 1 for GroundTheory.PAdicHodge.minpoly_map_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:04.850804+00:00
-- url     : https://prove2.me/submissions/19554407-d835-4b1a-acd9-8ec34dce1ff0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTraceFₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTraceₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {Ω : Type*} [Field Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (τ : F₁ ≃+* F₂) (σ : Ω ≃+* Ω) (h : ∀ a, algebraMap F₂ Ω (τ a) = σ (algebraMap F₁ Ω a))
    {y : Ω} (hy : IsIntegral F₁ y) :
    minpoly F₂ (σ y) = (minpoly F₁ y).map (τ : F₁ →+* F₂) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · have := (MulEquiv.irreducible_iff (Polynomial.mapEquiv τ)).2 (minpoly.irreducible hy)
    simpa using this
  · have hc : (algebraMap F₂ Ω).comp (τ : F₁ →+* F₂) = (σ : Ω →+* Ω).comp (algebraMap F₁ Ω) :=
      RingHom.ext h
    rw [aeval_def, eval₂_map, hc, ← RingEquiv.coe_toRingHom, ← hom_eval₂, ← aeval_def,
      minpoly.aeval, map_zero]
  · exact (minpoly.monic hy).map _
end GroundTheory.PAdicHodge
