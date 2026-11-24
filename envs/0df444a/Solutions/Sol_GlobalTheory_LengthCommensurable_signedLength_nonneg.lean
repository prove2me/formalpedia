-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:54.448811+00:00
-- url     : https://prove2.me/submissions/9c0ade6a-4a5b-4bed-a237-f77cd1c69db4

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
    0 ≤ signedLength A B := by
  rw [h.signedLength_of_ge hBA]
  exact Int.natCast_nonneg _
end GlobalTheory.LengthCommensurable
