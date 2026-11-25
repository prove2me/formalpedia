-- Prove2me | solution 1 for GroundTheory.LocalField.topologicalAbelianizationEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:15:34.094173+00:00
-- url     : https://prove2.me/submissions/74d34cd5-1430-4923-bee3-1595cf1d9bf7

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
variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (σ : Ω ≃ₐ[F] Ω) :
    topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension F Ω) σ :=
  rfl
end GroundTheory.LocalField
