-- Prove2me | solution 1 for GlobalTheory.TwoLines.logCol_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:15.855323+00:00
-- url     : https://prove2.me/submissions/2177c73d-6128-428b-8fe3-550946dec4fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumBoundedBelow
import Theorems.Thm_GlobalTheory_TwoLines_colSq_pos
import Theorems.Thm_GlobalTheory_TwoLines_det_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_det_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_two_le_inf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_entry_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution (X : Data E 2) {x0 : Frame X.Ψ 2} {τ : X.Ψ} (h : (mat x0 τ).det ≠ 0)
    (z : V (nd X)) : ContDiffAt ℝ 2 (fun w => Real.log (colSq (cpt X x0 w) τ)) z := by
  refine ContDiffAt.log ?_ (colSq_pos (by rwa [det_cpt])).ne'
  have hc : ∀ a, ContDiffAt ℝ 2 (fun w => ‖cpt X x0 w τ a 0‖ ^ 2) z := fun a =>
    (((IW.cpt_entry_cd X x0 τ a 0).restrict_scalars ℝ).of_le HE.two_le_inf).contDiffAt.norm_sq ℂ
  exact (hc 0).add (hc 1)
end GlobalTheory.TwoLines
