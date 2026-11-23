-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.val_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:03.545606+00:00
-- url     : https://prove2.me/submissions/11baef31-8a59-4941-a703-d15df5830cee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) {j : ℕ} (hj : j < s) :
    ((e * j : ℕ) : ZMod d).val = e * j := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  apply ZMod.val_cast_of_lt
  rw [← h, mul_comm s e]
  exact Nat.mul_lt_mul_of_pos_left hj he
end GlobalTheory.PeriodDvd
