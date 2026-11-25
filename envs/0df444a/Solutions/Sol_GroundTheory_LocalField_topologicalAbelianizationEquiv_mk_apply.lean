-- Prove2me | solution 1 for GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:36.754977+00:00
-- url     : https://prove2.me/submissions/ca41fa8a-424d-40c9-98bf-e3763195834b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_topologicalAbelianizationEquiv_mk

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
variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (σ : Ω ≃ₐ[F] Ω) (x : maximalAbelianExtension F Ω) :
    ((topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) x : _) : Ω) =
      σ x := by
  rw [topologicalAbelianizationEquiv_mk, AlgEquiv.restrictNormalHom_apply]
end GroundTheory.LocalField
