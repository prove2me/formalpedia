-- Prove2me | solution 1 for GlobalTheory.LeviZero.coord_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:24.252851+00:00
-- url     : https://prove2.me/submissions/5493aa08-edfb-48d5-9bf3-eabff2a292f5

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
theorem _root_.solution (m : Fin n) : ContDiff ℝ 2 (fun z : V n => z m) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ).contDiff (n := 2)).restrict_scalars ℝ
end GlobalTheory.LeviZero
