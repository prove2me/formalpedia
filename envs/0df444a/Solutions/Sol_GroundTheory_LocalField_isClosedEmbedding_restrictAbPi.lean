-- Prove2me | solution 1 for GroundTheory.LocalField.isClosedEmbedding_restrictAbPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:03.287208+00:00
-- url     : https://prove2.me/submissions/1d783972-4d03-4eab-9341-dc392da8d98d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_continuous_restrictAbPi
import Theorems.Thm_GroundTheory_LocalField_injective_restrictAbPi

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
namespace GroundTheory.LocalField
theorem _root_.solution : Topology.IsClosedEmbedding (restrictAbPi F Ω) := by
  have : ∀ L : finiteAbelianExtensions F Ω,
      T2Space ((L : IntermediateField F Ω) ≃ₐ[F] (L : IntermediateField F Ω)) := fun L => by
    have := L.2.2
    exact krullTopology_t2
  exact continuous_restrictAbPi.isClosedEmbedding injective_restrictAbPi
end GroundTheory.LocalField
