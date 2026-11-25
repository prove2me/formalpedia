-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_le_natCast_iff_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:59.126476+00:00
-- url     : https://prove2.me/submissions/6cd60e0f-8d83-4c0b-9071-b49eb57596c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution (h : LengthCommensurable A B) (hBA : B ≤ A) {n : ℕ} :
    signedLength A B ≤ n ↔ relLength A B ≤ n := by
  rw [h.signedLength_of_ge hBA, Nat.cast_le, ← ENat.coe_le_coe, ENat.coe_toNat h.1]
end GlobalTheory.LengthCommensurable
