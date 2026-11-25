-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_restrictAbPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:33.597691+00:00
-- url     : https://prove2.me/submissions/36c4eb05-5208-4943-9245-3ba07bb0c728

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_continuous_restrictAb

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
theorem _root_.solution : Continuous (restrictAbPi F Ω) :=
  continuous_pi fun L => by
    have := L.2.2
    exact continuous_restrictAb _ _
end GroundTheory.LocalField
