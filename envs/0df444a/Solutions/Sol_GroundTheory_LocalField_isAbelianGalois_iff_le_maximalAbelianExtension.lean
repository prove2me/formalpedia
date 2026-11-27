-- Prove2me | solution 1 for GroundTheory.LocalField.isAbelianGalois_iff_le_maximalAbelianExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:49:31.375104+00:00
-- url     : https://prove2.me/submissions/4a774ec9-1105-4eac-9f8e-48ba00db124e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_isAbelianGalois_of_le_maximalAbelianExtension

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
theorem _root_.solution (E : IntermediateField F Ω) [Normal F E] :
    IsAbelianGalois F E ↔ E ≤ maximalAbelianExtension F Ω :=
  ⟨fun _ => le_maximalAbelianExtension E, isAbelianGalois_of_le_maximalAbelianExtension E⟩
end GroundTheory.LocalField
