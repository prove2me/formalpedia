-- Prove2me | solution 1 for GroundTheory.LocalField.injective_restrictAbPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:28.977443+00:00
-- url     : https://prove2.me/submissions/0012c8e8-a760-4bae-8af9-ba620b83abea

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_ext_restrictAb

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
theorem _root_.solution : Function.Injective (restrictAbPi F Ω) := by
  intro σ τ hστ
  refine ext_restrictAb fun L _ _ => ?_
  exact congrFun hστ ⟨L, inferInstance, inferInstance⟩
end GroundTheory.LocalField
