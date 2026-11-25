-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.toNat_relLength_eq_add_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:54.351334+00:00
-- url     : https://prove2.me/submissions/5a509827-87d7-405f-a3df-a7b7ebc27acd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_of_between_left
import Theorems.Thm_GlobalTheory_LengthCommensurable_of_between_right

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
    (relLength A C).toNat = (relLength A B).toNat + (relLength B C).toNat := by
  rw [relLength_eq_add_of_le hCB hBA,
    ENat.toNat_add (h.of_between_left hCB hBA).1 (h.of_between_right hCB hBA).1]
end GlobalTheory.LengthCommensurable
