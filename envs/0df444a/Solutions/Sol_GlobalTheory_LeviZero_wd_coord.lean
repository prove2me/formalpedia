-- Prove2me | solution 1 for GlobalTheory.LeviZero.wd_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:55:32.315303+00:00
-- url     : https://prove2.me/submissions/f4a3dd6f-8d25-4d73-acb3-d86002ab8277

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_GlobalTheory_LeviZero_coord_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



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
theorem _root_.solution (m j : Fin n) (y : V n) : wd n j (fun z : V n => z m) y = if m = j then 1 else 0 := by
  rw [wd_of_differentiableAt (coord_diff m y)]
  have : fderiv ℂ (fun z : V n => z m) y = (EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ) :=
    (EuclideanSpace.proj (𝕜 := ℂ) m : V n →L[ℂ] ℂ).fderiv
  rw [this]
  simp [bas, Pi.single_apply]
end GlobalTheory.LeviZero
