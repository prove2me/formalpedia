-- Prove2me | solution 1 for GlobalTheory.ProperImmersionPoint.pnorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:56:33.443812+00:00
-- url     : https://prove2.me/submissions/339ec73b-f4ba-4f5d-888b-94c499b9a418

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_nfac_pos


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
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 * Real.exp (-phla X la x) := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  have e : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  have e2 : -phla X la x = ((2 : ℕ) : ℝ) * Real.log (X.nfac la x) := by
    unfold phla; push_cast; ring
  rw [e, e2, Real.exp_nat_mul, Real.exp_log hn, mul_pow]
end GlobalTheory.ProperImmersionPoint
