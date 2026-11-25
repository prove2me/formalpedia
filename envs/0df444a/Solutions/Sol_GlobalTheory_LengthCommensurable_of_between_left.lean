-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.of_between_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:48.668119+00:00
-- url     : https://prove2.me/submissions/16a4ff8f-bf60-47b5-8b03-36af89bc8fff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_lengthCommensurable_iff_of_le_of_le

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
variable {A A' B B' C : Submodule R V}
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A B :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).1
end GlobalTheory.LengthCommensurable
