-- Prove2me | solution 1 for GlobalTheory.ProperImmersionPoint.sum_pnorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:27:38.528708+00:00
-- url     : https://prove2.me/submissions/c399d537-3214-4448-8b13-156766b229eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CptDifferentiable
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_sum_pnorm_sq
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_sum_norm_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ProperImmersionPoint
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ProperImmersionPoint
theorem _root_.solution {r : ℕ} {X : Data E r} {L : Wt X.Ψ r} {N : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm L (w k) x ^ 2 := by
  rw [sum_pnorm_sq L w hx]
  exact mul_pos (sum_norm_pos hnz hx) (Real.exp_pos _)
end GlobalTheory.ProperImmersionPoint
