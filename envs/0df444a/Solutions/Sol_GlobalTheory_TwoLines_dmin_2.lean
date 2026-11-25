-- Prove2me | solution 1 for GlobalTheory.TwoLines.dmin_2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:04.714974+00:00
-- url     : https://prove2.me/submissions/db58bae5-d9e8-46f0-a880-e92bc55bff2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_GlobalTheory_TwoLines_det_mat
import Theorems.Thm_GlobalTheory_TwoLines_gram_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) :
    dmin 1 x τ 2 = (‖(mat x τ).det‖ ^ 2 : ℝ) := by
  have : dmin 1 x τ 2 = gram τ.1 1 (mat x τ) 0 0 * gram τ.1 1 (mat x τ) 1 1 -
      gram τ.1 1 (mat x τ) 0 1 * gram τ.1 1 (mat x τ) 1 0 := Matrix.det_fin_two _
  rw [this, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, det_mat]
  simp only [gram_one, map_sub, map_mul]
  ring
end GlobalTheory.TwoLines
