-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_map_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:31.043525+00:00
-- url     : https://prove2.me/submissions/17d22287-a966-4a41-b3d0-9a6760db9d58

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_minpoly_map_ringEquiv
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
theorem _root_.solution {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω]
    [Algebra F₂ Ω] (τ : F₁ ≃+* F₂) (σ : Ω ≃+* Ω)
    (h : ∀ a, algebraMap F₂ Ω (τ a) = σ (algebraMap F₁ Ω a)) {y : Ω} (hy : IsIntegral F₁ y) :
    normTrace F₂ (σ y) = σ (normTrace F₁ y) := by
  rw [normTrace, normTraceF, minpoly_map_ringEquiv τ σ h hy, nextCoeff_map τ.injective,
    natDegree_map_eq_of_injective τ.injective, normTrace, normTraceF, ← h]
  simp [map_div₀, map_neg, map_natCast]
end GroundTheory.PAdicHodge
