-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:35.87897+00:00
-- url     : https://prove2.me/submissions/6b5a67d3-5956-4b89-9ba7-d4aece64c2dc

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
theorem _root_.solution (a : A) (x y : Fin n → A) : ip c (a • x) y = a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.GramCount
