-- Prove2me | solution 1 for GlobalTheory.CycFr.act_nat_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:59.700856+00:00
-- url     : https://prove2.me/submissions/25d7e31e-2745-4c94-8463-8f9a1ef217c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_X
import Theorems.Thm_GlobalTheory_CycFr_bin_nat

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
omit [IsDomain O] [CharZero O]
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (d : ℕ) : _root_.GlobalTheory.CycFr.act O (d : ℤ_[l]) X = (1 + X) ^ d - 1 := by
  rw [_root_.GlobalTheory.CycFr.act_X, _root_.GlobalTheory.CycFr.bin_nat]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
