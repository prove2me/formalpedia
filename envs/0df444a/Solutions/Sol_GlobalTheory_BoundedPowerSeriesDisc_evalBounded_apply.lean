-- Prove2me | solution 1 for GlobalTheory.BoundedPowerSeriesDisc.evalBounded_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:10.492429+00:00
-- url     : https://prove2.me/submissions/6b50a6c1-b8fe-42fb-b2ee-d5a25d997891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BoundedPowerSeriesDisc
open PowerSeries
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
variable [CompleteSpace F]
variable (π : F) (hπ : ‖π‖ < 1)
namespace GlobalTheory.BoundedPowerSeriesDisc
theorem _root_.solution (f : boundedSeries F) :
    evalBounded π hπ f = ∑' n, coeff n (f : F⟦X⟧) * π ^ n := rfl
end GlobalTheory.BoundedPowerSeriesDisc
