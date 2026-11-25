-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:24.764433+00:00
-- url     : https://prove2.me/submissions/8f383853-0f94-4323-af32-a64efbcd1d83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}
namespace GlobalTheory.GramCount
theorem _root_.solution (x : Fin n → A) : ip c x 0 = 0 := by
  simp [ip]
end GlobalTheory.GramCount
