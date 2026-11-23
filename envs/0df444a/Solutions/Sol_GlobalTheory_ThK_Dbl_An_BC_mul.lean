-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.BC.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:06.047442+00:00
-- url     : https://prove2.me/submissions/b153844b-287f-429a-beaa-0d2aa9b9157e

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
theorem _root_.solution (h : BC f) (h' : BC g) : BC fun x => f x * g x := by
  obtain ⟨a, C, hC⟩ := h
  obtain ⟨b, C', hC'⟩ := h'
  exact ⟨a.mul b, C * C', fun x => (norm_mul_le _ _).trans
    (mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))⟩
end BC
end GlobalTheory.ThK.Dbl.An
