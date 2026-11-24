-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.det_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:10.573477+00:00
-- url     : https://prove2.me/submissions/907fe53c-a80c-4ac5-bc19-872efdaaf1f7

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
theorem _root_.solution (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : (blk a b h).det = a * h.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have : (blk a b h).submatrix Fin.succ Fin.succ = h := by ext i j; simp [blk]
  simp [blk] at this ⊢
  simp [this]
end GlobalTheory.ThK.Dbl.LD
