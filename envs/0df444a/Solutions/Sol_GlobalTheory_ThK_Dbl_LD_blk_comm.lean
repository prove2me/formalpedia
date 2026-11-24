-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.blk_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:46.894087+00:00
-- url     : https://prove2.me/submissions/ac74e50b-683e-476e-9529-dd19d7e9515a

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
theorem _root_.solution (a : k) (b b' : Fin d → k) (hb : b = (a - 1) • b') :
    blk a 0 1 * blk 1 b' 1 = blk 1 b 1 * (blk 1 b' 1 * blk a 0 1) := by
  subst hb
  ext i j
  rw [← Matrix.mul_assoc]
  refine Fin.cases ?_ (fun j => ?_) j <;> simp only [mul_blk_zero, mul_blk_succ] <;>
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [blk, one_apply]
  ring
end GlobalTheory.ThK.Dbl.LD
