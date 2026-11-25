-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_zero_iff_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:07:41.803784+00:00
-- url     : https://prove2.me/submissions/b605a4c0-4e32-497b-a34c-a2d48984fbc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_natCast_iff_of_ge

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
    signedLength A B = 0 ↔ A = B := by
  have := h.signedLength_eq_natCast_iff_of_ge hBA (n := 0)
  rw [Nat.cast_zero, Nat.cast_zero, relLength_eq_zero_iff] at this
  exact this.trans ⟨fun hAB => le_antisymm hAB hBA, le_of_eq⟩
end GlobalTheory.LengthCommensurable
