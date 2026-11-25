-- Prove2me | solution 1 for GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:14.662257+00:00
-- url     : https://prove2.me/submissions/a8e786dd-fad1-4c3a-ac1f-8f581dfcc789

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Theorems.Thm_GlobalTheory_ClosedDiscontinuity_propDisc_closed
import Theorems.Thm_GlobalTheory_ClosedDiscontinuity_firstMinimum_invariant_continuous_pos_on_frames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ClosedDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ClosedDiscontinuity
namespace _root_.GlobalTheory.ClosedDiscontinuity
theorem _root_.solution :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) ∧ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration (E := E)) :=
  ⟨_root_.GlobalTheory.ClosedDiscontinuity.propDisc_closed, _root_.GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames⟩
end _root_.GlobalTheory.ClosedDiscontinuity
end GlobalTheory.ClosedDiscontinuity
