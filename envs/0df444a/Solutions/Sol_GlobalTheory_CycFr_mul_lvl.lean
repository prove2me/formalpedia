-- Prove2me | solution 1 for GlobalTheory.CycFr.mul_lvl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:19.377584+00:00
-- url     : https://prove2.me/submissions/f4fa5703-3a7b-49f3-a982-10e6553103c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
omit [Fact l.Prime] [Algebra ℤ_[l] O] [IsDomain O] [CharZero O]
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (k : ℕ) :
    ((1 + X : O⟦X⟧) ^ l ^ k - 1) * _root_.GlobalTheory.CycFr.lvl l O k = (1 + X) ^ l ^ (k + 1) - 1 := by
  rw [_root_.GlobalTheory.CycFr.lvl, mul_comm, geom_sum_mul, ← pow_mul, ← pow_succ]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
