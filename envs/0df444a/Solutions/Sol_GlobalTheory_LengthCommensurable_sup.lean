-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:52.884654+00:00
-- url     : https://prove2.me/submissions/abcaf1fb-b44c-4690-8624-237b71bc7134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_relLength_sup_ne_top_iff

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
    LengthCommensurable (A ⊔ B) (A' ⊔ B') :=
  ⟨relLength_sup_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.1 (relLength_anti_right A le_sup_left),
        ne_top_of_le_ne_top hB.1 (relLength_anti_right B le_sup_right)⟩,
    relLength_sup_ne_top_iff.mpr
      ⟨ne_top_of_le_ne_top hA.2 (relLength_anti_right A' le_sup_left),
        ne_top_of_le_ne_top hB.2 (relLength_anti_right B' le_sup_right)⟩⟩
end GlobalTheory.LengthCommensurable
