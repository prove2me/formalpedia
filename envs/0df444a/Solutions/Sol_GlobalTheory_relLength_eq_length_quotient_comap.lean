-- Prove2me | solution 1 for GlobalTheory.relLength_eq_length_quotient_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:21.732487+00:00
-- url     : https://prove2.me/submissions/a50bbde2-b3e7-4223-9e6c-dfdf16e6854f

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
theorem _root_.solution (A B : Submodule R V) :
    relLength A B = Module.length R (A ⧸ B.comap A.subtype) := rfl
end GlobalTheory
