-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.chE_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:50.665768+00:00
-- url     : https://prove2.me/submissions/11e4a5f1-5bbb-4472-9b02-31ad624c9eb8

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
theorem _root_.solution (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) (b : Fin d → k) :
    chE (X * blk 1 b 1) = (((chE X).1.1, (chE X).1.2 + b), (chE X).2) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j; simp [chE, mul_blk_zero, mul_blk_succ, one_apply]; field_simp; ring
  · ext i j; simp [chE, mul_blk_zero, mul_blk_succ, one_apply]; field_simp; ring
end GlobalTheory.ThK.Dbl.LD
