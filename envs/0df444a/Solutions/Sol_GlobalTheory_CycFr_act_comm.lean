-- Prove2me | solution 1 for GlobalTheory.CycFr.act_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:28.518533+00:00
-- url     : https://prove2.me/submissions/6bd88856-7bf4-490e-9d28-40d8937f2c04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_mul

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
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (c d : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.act O d a) = _root_.GlobalTheory.CycFr.act O d (_root_.GlobalTheory.CycFr.act O c a) := by
  rw [← _root_.GlobalTheory.CycFr.act_mul, ← _root_.GlobalTheory.CycFr.act_mul, mul_comm]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
