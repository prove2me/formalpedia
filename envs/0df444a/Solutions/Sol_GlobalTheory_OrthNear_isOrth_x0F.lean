-- Prove2me | solution 1 for GlobalTheory.OrthNear.isOrth_x0F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:16.525657+00:00
-- url     : https://prove2.me/submissions/ab15b21d-dff1-4c04-91fb-79c2357d1bd5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DminCptEq

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
open GlobalTheory GlobalTheory.OrthNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.OrthNear
namespace _root_.GlobalTheory.OrthNear
theorem _root_.solution {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth
  intro τ
  generalize_proofs h
  exact (h τ).choose_spec.2
end _root_.GlobalTheory.OrthNear
end GlobalTheory.OrthNear
