-- Prove2me | solution 1 for GlobalTheory.relLength_eq_add_sup_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:53.656344+00:00
-- url     : https://prove2.me/submissions/5a0d5ef6-2bac-42a3-9192-6ce7961996bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_relLength_sup_eq_add

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
theorem _root_.solution {A B : Submodule R V} (hBA : B ≤ A) (C : Submodule R V) :
    relLength A C = relLength A (B ⊔ C) + relLength B C := by
  rw [← relLength_sup_eq_add, sup_eq_left.mpr hBA]
end GlobalTheory
