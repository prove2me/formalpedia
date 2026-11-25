-- Prove2me | solution 1 for GlobalTheory.LeviZero.coord_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:09.637797+00:00
-- url     : https://prove2.me/submissions/205482cd-858e-4595-be07-9597ba439443

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal

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
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
variable {ξ : Fin n → ℂ} {x : V n}
namespace GlobalTheory.LeviZero
theorem _root_.solution (m : Fin n) : Differentiable ℂ (fun z : V n => z m) :=
  (EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ).differentiable
end GlobalTheory.LeviZero
