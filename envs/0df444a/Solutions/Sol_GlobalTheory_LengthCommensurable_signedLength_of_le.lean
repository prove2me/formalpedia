-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:40:02.49106+00:00
-- url     : https://prove2.me/submissions/21fa8b2e-6241-4965-9be6-52a55b7ab9e6

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
theorem _root_.solution (_h : LengthCommensurable A B) (hAB : A ≤ B) :
    signedLength A B = -((relLength B A).toNat : ℤ) := by
  simp [signedLength, relLength_eq_zero_of_le hAB]
end GlobalTheory.LengthCommensurable
