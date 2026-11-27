-- Prove2me | solution 2 for GroundTheory.LocalField.mem_finiteAbelianExtensions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:11.803133+00:00
-- url     : https://prove2.me/submissions/6656b2e2-7ef0-4daf-91e1-96203a735085

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
omit [IsGalois F Ω]
namespace GroundTheory.LocalField
theorem _root_.solution {L : IntermediateField F Ω} :
    L ∈ finiteAbelianExtensions F Ω ↔ FiniteDimensional F L ∧ IsAbelianGalois F L :=
  Iff.rfl
end GroundTheory.LocalField
