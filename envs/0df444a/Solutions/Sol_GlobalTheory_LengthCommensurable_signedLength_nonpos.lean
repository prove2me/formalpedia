-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:46.687259+00:00
-- url     : https://prove2.me/submissions/7a55d714-24ea-4f92-9a6f-df21006a3d2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_of_le

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
theorem _root_.solution (h : LengthCommensurable A B) (hAB : A ≤ B) :
    signedLength A B ≤ 0 := by
  rw [h.signedLength_of_le hAB, neg_nonpos]
  exact Int.natCast_nonneg _
end GlobalTheory.LengthCommensurable
