-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_add_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:06.035051+00:00
-- url     : https://prove2.me/submissions/4d0ca16a-348e-4863-aa34-497fd01af334

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
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution (h : LengthCommensurable A B) :
    signedLength A B + signedLength B A = 0 := by
  rw [h.signedLength_swap, add_neg_cancel]
end GlobalTheory.LengthCommensurable
