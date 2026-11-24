-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.chE_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:49.703858+00:00
-- url     : https://prove2.me/submissions/2b343664-a8cc-4738-9cb6-d46043215296

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_mul_blk_zero
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_mul_blk_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] {n d : ℕ}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (h : Matrix (Fin d) (Fin d) k) :
    chE (X * blk 1 0 h) = (((chE X).1.1, (chE X).1.2 ᵥ* h), (chE X).2 * h) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j
    simp only [chE, mul_blk_zero, mul_blk_succ, vecMul, dotProduct, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  · ext i j
    simp only [chE, mul_blk_zero, mul_blk_succ, of_apply, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    rw [mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp only [of_apply]; ring
end GlobalTheory.ThK.Dbl.LD
