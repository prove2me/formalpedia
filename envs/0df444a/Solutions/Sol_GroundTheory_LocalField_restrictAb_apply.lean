-- Prove2me | solution 1 for GroundTheory.LocalField.restrictAb_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:36:28.418823+00:00
-- url     : https://prove2.me/submissions/149fa4c8-d899-4d80-882d-9c6d105629ae

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_topologicalAbelianizationEquiv_mk_apply
import Theorems.Thm_GroundTheory_LocalField_restrictAb_topologicalAbelianizationEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (E : IntermediateField F Ω) [Normal F E]
namespace GroundTheory.LocalField
theorem _root_.solution (h : E ≤ maximalAbelianExtension F Ω) (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) (x : E) :
    ((restrictAb E h σ x : E) : Ω) = ((σ ⟨x, h x.2⟩ : maximalAbelianExtension F Ω) : Ω) := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective ((topologicalAbelianizationEquiv F Ω).symm σ)
  have hσ : σ = topologicalAbelianizationEquiv F Ω (τ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) := by
    rw [hτ, ContinuousMulEquiv.apply_symm_apply]
  rw [hσ, restrictAb_topologicalAbelianizationEquiv, AlgEquiv.restrictNormalHom_apply,
    topologicalAbelianizationEquiv_mk_apply]
end GroundTheory.LocalField
