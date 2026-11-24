-- Prove2me | solution 1 for GlobalTheory.relLength_map_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:21.005515+00:00
-- url     : https://prove2.me/submissions/a9f71207-071a-4d33-b632-1f00f4138eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory
theorem _root_.solution (W : Submodule R V) (A B : Submodule R W) :
    relLength (A.map W.subtype) (B.map W.subtype) = relLength A B :=
  relLength_map_of_injective W.subtype W.injective_subtype A B
end GlobalTheory
