-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:05.215857+00:00
-- url     : https://prove2.me/submissions/8a1f79c7-0fd3-4022-ba8d-fc9cfeba5646

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
theorem _root_.solution (hAB : LengthCommensurable A B) (hBC : LengthCommensurable B C) :
    signedLength A B + signedLength B C = signedLength A C :=
  (hAB.signedLength_eq_add hBC).symm
end GlobalTheory.LengthCommensurable
