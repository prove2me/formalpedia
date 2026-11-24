-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.cont_chE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:02.38027+00:00
-- url     : https://prove2.me/submissions/d901265d-65da-4637-92ce-e620050eadd4

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
variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution : ContinuousOn (chE (k := k) (n := n) (d := d)) {X | X 0 0 ≠ 0} := by
  have h : ∀ j : Fin d, ContinuousOn (fun X : Matrix (Fin (n + 1)) (Fin (d + 1)) k => X 0 j.succ / X 0 0) {X | X 0 0 ≠ 0} :=
    fun j => ContinuousOn.div (by fun_prop) (by fun_prop) fun _ h => h
  refine ContinuousOn.prodMk (ContinuousOn.prodMk (by fun_prop) (continuousOn_pi.2 h))
    (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_)
  exact ContinuousOn.sub (by fun_prop) (ContinuousOn.mul (by fun_prop) (h j))
end GlobalTheory.ThK.Dbl.LD
