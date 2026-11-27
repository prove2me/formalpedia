-- Prove2me | solution 2 for GlobalTheory.relLength_inf_eq_relLength_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:59.227594+00:00
-- url     : https://prove2.me/submissions/f7530652-66b8-4bd2-a800-ba72e1bcd6ac

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
    relLength A (A ⊓ B) = relLength (A ⊔ B) B := by simp
end GlobalTheory
