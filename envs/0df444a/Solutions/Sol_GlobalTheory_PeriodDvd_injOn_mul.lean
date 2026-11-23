-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.injOn_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:38.151265+00:00
-- url     : https://prove2.me/submissions/33923862-b7b6-42dd-a476-cf6b92b41ce9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_val_mul

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
theorem _root_.solution {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    Set.InjOn (fun j => ((e * j : ℕ) : ZMod d)) (Finset.range s : Set ℕ) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  intro i hi j hj hij
  have hi' : i < s := by simpa using hi
  have hj' : j < s := by simpa using hj
  have := congrArg ZMod.val hij
  simp only at this
  rw [val_mul h hi', val_mul h hj'] at this
  exact Nat.eq_of_mul_eq_mul_left he this
end GlobalTheory.PeriodDvd
