-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.cont_chR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:02.5244+00:00
-- url     : https://prove2.me/submissions/b749d979-ea1f-4b3c-8850-c28cb0b2bf00

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
theorem _root_.solution : Continuous (chR (k := k) (n := n) (d := d)) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR] <;> fun_prop
end GlobalTheory.ThK.Dbl.LD
