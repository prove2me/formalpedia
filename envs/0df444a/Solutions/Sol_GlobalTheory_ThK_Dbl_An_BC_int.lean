-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.BC.int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:05.726852+00:00
-- url     : https://prove2.me/submissions/478021b8-5573-45c4-b974-48e4e8ca7e50

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FarRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
variable {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {f g : X → ℂ}
namespace GlobalTheory.ThK.Dbl.An
namespace BC
theorem _root_.solution [MeasurableSpace X] [OpensMeasurableSpace X] (h : BC f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ :=
  .of_bound h.1.aestronglyMeasurable _ (.of_forall h.2.choose_spec)
end BC
end GlobalTheory.ThK.Dbl.An
