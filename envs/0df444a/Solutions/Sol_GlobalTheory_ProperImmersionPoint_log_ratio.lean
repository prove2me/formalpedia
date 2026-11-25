-- Prove2me | solution 1 for GlobalTheory.ProperImmersionPoint.log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:05:08.311695+00:00
-- url     : https://prove2.me/submissions/035b5837-1c41-4909-aa38-03fd7d40424d

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
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_phla_lin
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_sum_pnorm_sq
import Theorems.Thm_GlobalTheory_ProperImmersionPoint_sum_norm_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


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
    (h : et x ≠ 0) : Real.log (ratio X L eW a w et x) =
      Real.log (Complex.normSq (et x)) + phla X (a • L - eW) x +
        (-(a : ℝ)) * Real.log (∑ k, ‖w k x‖ ^ 2) := by
  have hA : 0 < ‖et x‖ ^ 2 := pow_pos (norm_pos_iff.2 h) 2
  have hW := sum_norm_pos hnz hx
  unfold ratio
  rw [phla_lin X hx, pnorm_sq X _ _ hx, sum_pnorm_sq L w hx,
    Real.log_div (mul_pos hA (Real.exp_pos _)).ne' (pow_pos (mul_pos hW (Real.exp_pos _)) _).ne',
    Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow _ a,
    Real.log_mul hW.ne' (Real.exp_pos _).ne', Real.log_exp, Complex.normSq_eq_norm_sq]
  ring
end GlobalTheory.ProperImmersionPoint
