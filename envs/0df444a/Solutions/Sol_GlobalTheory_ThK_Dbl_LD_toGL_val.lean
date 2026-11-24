-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.toGL_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:33.212406+00:00
-- url     : https://prove2.me/submissions/d02997b4-dbed-407d-bc1b-8c0f7259cd4c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE

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
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {X : Matrix (Fin d) (Fin d) k} (h : X.det ≠ 0) : (toGL X).1 = X := by
  rw [toGL, dif_pos ((isUnit_iff_isUnit_det X).2 h.isUnit)]; rfl
end GlobalTheory.ThK.Dbl.LD
