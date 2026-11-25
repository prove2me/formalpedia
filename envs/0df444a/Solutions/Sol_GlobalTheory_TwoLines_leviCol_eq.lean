-- Prove2me | solution 1 for GlobalTheory.TwoLines.leviCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:20.751922+00:00
-- url     : https://prove2.me/submissions/a0b09f69-655f-41f1-98e6-84d0efbe4e9c

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
import Theorems.Thm_GlobalTheory_TwoLines_wd_affine
import Theorems.Thm_GlobalTheory_TwoLines_colSq_pos
import Theorems.Thm_GlobalTheory_TwoLines_compact_frame_first_column
import Theorems.Thm_GlobalTheory_TwoLines_det_cpt
import Theorems.Thm_GlobalTheory_TwoLines_det_mat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_det_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviLogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviLogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sqNorm_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution (X : Data E 2) {x0 : Frame X.Ψ 2} {τ : X.Ψ} (h : (mat x0 τ).det ≠ 0)
    (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    0 ≤ leviCol X x0 τ z ξ ∧ (ξ (idx X τ) ≠ 0 → 0 < leviCol X x0 τ z ξ) := by
  let g : Fin 2 → V (nd X) → ℂ := fun a w => x0 τ a 0 + x0 τ a 1 * w (idx X τ)
  have hs : ∀ w, colSq (cpt X x0 w) τ = sqNorm fun a => g a w := fun w => by
    simp [colSq, sqNorm, compact_frame_first_column, g, Complex.normSq_eq_norm_sq]
  have hpos : 0 < sqNorm fun a => g a z := hs z ▸ colSq_pos (by rwa [det_cpt])
  have hne : (fun a => g a z) ≠ 0 := fun h0 => by rw [h0] at hpos; simp [sqNorm] at hpos
  have hcd : ∀ a, ContDiffAt ℂ 2 (g a) z := fun a =>
    (contDiff_const.add (contDiff_const.mul
      (EuclideanSpace.proj (idx X τ) : V (nd X) →L[ℂ] ℂ).contDiff)).contDiffAt
  have hL := leviLogNormSq (nd X) 2 g z ξ hcd hne
  have hJ : wJac (nd X) 2 g z *ᵥ ξ = fun a => x0 τ a 1 * ξ (idx X τ) := by
    funext a
    simp [wJac, Matrix.mulVec, dotProduct, g, wd_affine]
  unfold leviCol
  simp only [hs]
  rw [hL, Complex.ofReal_re, hJ]
  refine ⟨div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) hpos.le, fun hξ =>
    div_pos (sqNorm_pos fun h0 => ?_) hpos⟩
  rw [projPerp_mulVec] at h0
  set c := ((sqNorm fun a => g a z : ℝ) : ℂ)⁻¹ * (star (fun a => g a z) ⬝ᵥ fun a => x0 τ a 1 * ξ (idx X τ))
  have e0 : x0 τ 0 1 * ξ (idx X τ) - c * (x0 τ 0 0 + x0 τ 0 1 * z (idx X τ)) = 0 := congrFun h0 0
  have e1 : x0 τ 1 1 * ξ (idx X τ) - c * (x0 τ 1 0 + x0 τ 1 1 * z (idx X τ)) = 0 := congrFun h0 1
  rw [det_mat] at h
  have hc : c = 0 := by
    apply (mul_eq_zero_iff_right h).1
    linear_combination x0 τ 0 1 * e1 - x0 τ 1 1 * e0
  apply mul_ne_zero h hξ
  rw [hc] at e0 e1
  linear_combination x0 τ 0 0 * e1 - x0 τ 1 0 * e0
end GlobalTheory.TwoLines
