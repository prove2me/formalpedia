-- Prove2me | solution 1 for GlobalTheory.relLength_sup_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:26.343932+00:00
-- url     : https://prove2.me/submissions/803453ef-068e-424e-bbfa-c924a570e2fb

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
theorem _root_.solution (A B C : Submodule R V) :
    relLength (A ⊔ B) C = relLength A (B ⊔ C) + relLength B C := by
  have h := relLength_eq_add_of_le (A := A ⊔ (B ⊔ C)) (B := B ⊔ C) (C := C) le_sup_right
    le_sup_right
  rwa [relLength_sup_left, relLength_sup_left, ← sup_assoc, relLength_sup_left] at h
end GlobalTheory
