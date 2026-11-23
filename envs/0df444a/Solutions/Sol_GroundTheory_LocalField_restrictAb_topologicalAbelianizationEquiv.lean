-- Prove2me | solution 1 for GroundTheory.LocalField.restrictAb_topologicalAbelianizationEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:28.035077+00:00
-- url     : https://prove2.me/submissions/f6c1672e-86f0-42e0-9ca7-c4597f2f9d09

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension

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
theorem _root_.solution (h : E ≤ maximalAbelianExtension F Ω) (σ : Ω ≃ₐ[F] Ω) :
    restrictAb E h (topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω))) =
      AlgEquiv.restrictNormalHom E σ := by
  change QuotientGroup.lift _ _ (closure_commutator_le_ker_restrictNormalHom E h)
    ((topologicalAbelianizationEquiv F Ω).symm (topologicalAbelianizationEquiv F Ω _)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl
end GroundTheory.LocalField
