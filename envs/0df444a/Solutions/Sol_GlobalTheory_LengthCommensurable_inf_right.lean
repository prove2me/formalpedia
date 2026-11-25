-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.inf_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:11:54.175874+00:00
-- url     : https://prove2.me/submissions/b2b774fe-c3a0-40e3-8fbf-dc4e0cd45d77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_relLength_inf_ne_top_iff

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
theorem _root_.solution (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊓ C) :=
  ⟨relLength_inf_ne_top_iff.mpr ⟨hAB.1, hAC.1⟩,
    ne_top_of_le_ne_top hAB.2 (relLength_mono_left inf_le_left A)⟩
end GlobalTheory.LengthCommensurable
