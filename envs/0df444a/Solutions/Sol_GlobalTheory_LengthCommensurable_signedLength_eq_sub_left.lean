-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:59.553498+00:00
-- url     : https://prove2.me/submissions/b0154862-fd6f-4c78-833a-0ce9ac74ff53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_add

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
theorem _root_.solution (hCA : LengthCommensurable C A) (hCB : LengthCommensurable C B) :
    signedLength A B = signedLength C B - signedLength C A := by
  rw [hCA.symm.signedLength_eq_add hCB, hCA.signedLength_swap, neg_add_eq_sub]
end GlobalTheory.LengthCommensurable
