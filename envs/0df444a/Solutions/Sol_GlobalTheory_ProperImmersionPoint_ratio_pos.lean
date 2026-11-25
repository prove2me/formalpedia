-- Prove2me | solution 1 for GlobalTheory.ProperImmersionPoint.ratio_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:38:02.212732+00:00
-- url     : https://prove2.me/submissions/1563206a-337c-4901-bc80-515c5d469409

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
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_pnorm_sq
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_sum_pnorm_pos

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
theorem _root_.solution {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : et x ≠ 0) : 0 < ratio X L eW a w et x := by
  refine div_pos ?_ (pow_pos (sum_pnorm_pos hnz hx) _)
  rw [pnorm_sq X _ _ hx]
  exact mul_pos (pow_pos (norm_pos_iff.2 h) 2) (Real.exp_pos _)
end GlobalTheory.ProperImmersionPoint
