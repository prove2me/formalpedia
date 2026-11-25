-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:51.808664+00:00
-- url     : https://prove2.me/submissions/9e962f7b-117a-4aa6-a784-23bc64799011

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
theorem _root_.solution (hA : LengthCommensurable A A') (hB : LengthCommensurable B B') :
    LengthCommensurable (A ⊓ B) (A' ⊓ B') :=
  ⟨relLength_inf_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.1 (relLength_mono_left inf_le_left A'),
        ne_top_of_le_ne_top hB.1 (relLength_mono_left inf_le_right B')⟩,
    relLength_inf_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.2 (relLength_mono_left inf_le_left A),
        ne_top_of_le_ne_top hB.2 (relLength_mono_left inf_le_right B)⟩⟩
end GlobalTheory.LengthCommensurable
