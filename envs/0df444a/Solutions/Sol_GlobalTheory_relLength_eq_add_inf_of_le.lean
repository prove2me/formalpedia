-- Prove2me | solution 1 for GlobalTheory.relLength_eq_add_inf_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:43.966403+00:00
-- url     : https://prove2.me/submissions/b77af7a5-b983-4b93-a981-ca0b536b3064

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe

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
theorem _root_.solution (A : Submodule R V) {B C : Submodule R V} (hCB : C ≤ B) :
    relLength A C = relLength A B + relLength (A ⊓ B) C := by
  rw [← relLength_inf_eq_add, inf_eq_right.mpr hCB]
end GlobalTheory
