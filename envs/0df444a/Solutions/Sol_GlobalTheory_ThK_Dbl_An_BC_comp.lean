-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.BC.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:23.55146+00:00
-- url     : https://prove2.me/submissions/f3d11e03-1d9a-4365-9612-ae46c2a2944e

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
theorem _root_.solution (h : BC f) {u : X' → X} (hu : Continuous u) : BC fun x => f (u x) := ⟨h.1.comp hu, h.2.imp fun _ h _ => h _⟩
end BC
end GlobalTheory.ThK.Dbl.An
