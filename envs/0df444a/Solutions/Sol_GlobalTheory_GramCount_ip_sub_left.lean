-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:51.701998+00:00
-- url     : https://prove2.me/submissions/e51c0e83-7b8d-4bc1-a9b0-863aa7cf5f29

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
theorem _root_.solution (x x' y : Fin n → A) : ip c (x - x') y = ip c x y - ip c x' y := by
  simp only [ip, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end GlobalTheory.GramCount
