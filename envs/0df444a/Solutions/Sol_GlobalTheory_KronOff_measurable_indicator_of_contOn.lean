-- Prove2me | solution 1 for GlobalTheory.KronOff.measurable_indicator_of_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:25.767574+00:00
-- url     : https://prove2.me/submissions/4d15637e-0665-4bad-b16f-a06e1bb34720

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableIndicatorOfContOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.KronOff
theorem _root_.solution {α : Type} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {U : Set α} (hU : IsOpen U) {f : α → ℝ} (hf : ContinuousOn f U) :
    Measurable (U.indicator f) := by
  classical
  refine measurable_of_restrict_of_restrict_compl hU.measurableSet ?_ ?_
  · have h : U.domRestrict (U.indicator f) = U.domRestrict f := by
      funext x
      show U.indicator f (x : α) = f x
      rw [Set.indicator_apply, if_pos x.2]
    rw [h]
    exact hf.restrict.measurable
  · have h : Uᶜ.domRestrict (U.indicator f) = fun _ => 0 := by
      funext x
      have hx : (x : α) ∉ U := x.2
      show U.indicator f (x : α) = 0
      rw [Set.indicator_apply, if_neg hx]
    rw [h]
    exact measurable_const
end GlobalTheory.KronOff
