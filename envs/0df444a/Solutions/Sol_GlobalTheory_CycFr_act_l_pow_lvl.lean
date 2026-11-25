-- Prove2me | solution 1 for GlobalTheory.CycFr.act_l_pow_lvl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:59.172554+00:00
-- url     : https://prove2.me/submissions/adaf88af-1664-4ad4-80b5-f335217b84e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_one_add_X
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
theorem _root_.solution (k : ℕ) : _root_.GlobalTheory.CycFr.act O ((l : ℤ_[l]) ^ k) (_root_.GlobalTheory.CycFr.lvl l O 0) = _root_.GlobalTheory.CycFr.lvl l O k := by
  have hb : _root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k) = (1 + X) ^ l ^ k := by
    rw [← Nat.cast_pow, _root_.GlobalTheory.CycFr.bin_nat]
  rw [_root_.GlobalTheory.CycFr.lvl, _root_.GlobalTheory.CycFr.lvl, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, pow_zero, pow_one, _root_.GlobalTheory.CycFr.act_one_add_X, hb]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
