-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:14.832052+00:00
-- url     : https://prove2.me/submissions/7454bc2d-5f6c-4e47-8097-12f03939016c

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
theorem _root_.solution (hAC : LengthCommensurable A C) (hBC : LengthCommensurable B C) :
    signedLength A B = signedLength A C - signedLength B C := by
  rw [hAC.signedLength_eq_add hBC.symm, hBC.signedLength_swap, sub_eq_add_neg]
end GlobalTheory.LengthCommensurable
