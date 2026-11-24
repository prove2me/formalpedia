-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.mul_blk_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:30.960551+00:00
-- url     : https://prove2.me/submissions/34521a68-2bbf-484f-aefe-71621c7185a4

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC

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
theorem _root_.solution {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m) :
    (X * blk a b h) i 0 = X i 0 * a := by simp [mul_apply, Fin.sum_univ_succ, blk]
end GlobalTheory.ThK.Dbl.LD
