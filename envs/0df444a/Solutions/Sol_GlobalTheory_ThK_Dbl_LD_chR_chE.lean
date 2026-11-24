-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.chR_chE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:21.181075+00:00
-- url     : https://prove2.me/submissions/501411be-5223-4294-a808-b6bdb909b5a5

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
theorem _root_.solution (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) : chR (chE X) = X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR, chE]
  field_simp
end GlobalTheory.ThK.Dbl.LD
