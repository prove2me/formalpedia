-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.coe_toNat_signedLength_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:00:23.897141+00:00
-- url     : https://prove2.me/submissions/0cd6615a-e2ad-497c-bdd4-291a7420662a

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
theorem _root_.solution (h : LengthCommensurable A B) (hBA : B ≤ A) :
    ((signedLength A B).toNat : ℕ∞) = relLength A B := by
  rw [h.signedLength_of_ge hBA, Int.toNat_natCast, ENat.coe_toNat h.1]
end GlobalTheory.LengthCommensurable
