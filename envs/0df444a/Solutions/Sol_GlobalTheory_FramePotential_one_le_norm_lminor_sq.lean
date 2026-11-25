-- Prove2me | solution 1 for GlobalTheory.FramePotential.one_le_norm_lminor_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:25.25453+00:00
-- url     : https://prove2.me/submissions/32da933b-7639-481a-be97-7e4bf9d96b64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OneLeMinorOfIsOrth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdFsq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_det_one_add_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_normSq_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_trace_ctm
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
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder
open GlobalTheory GlobalTheory.FramePotential
namespace GlobalTheory.FramePotential
theorem _root_.solution {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * (Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) * g.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    1 ≤ ‖lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2 := by
  set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA
  set C : Matrix (Fin n) (Fin p) ℂ :=
    Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC
  have key : Aᴴ * A = 1 + Cᴴ * C := by
    ext a b
    have e := congrFun (congrFun hg (Fin.castLE h b)) (Fin.castLE h a)
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.diagonal_apply, Fin.castLE_inj] at e
    have e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b =
        ∑ k, g k (Fin.castLE h b) * ((sgn p (k : ℕ) : ℝ) : ℂ) * starRingEnd ℂ (g k (Fin.castLE h a)) := by
      rw [e, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [sgn]
      · rw [if_neg hab, if_neg (Ne.symm hab)]
    have e2 : (Aᴴ * A) a b = ∑ k : Fin n, if (k : ℕ) < p then
        starRingEnd ℂ (g k (Fin.castLE h a)) * g k (Fin.castLE h b) else 0 := by
      rw [Matrix.mul_apply]
      refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
        (fun k => ?_)
      · rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
      · simp [hA, Matrix.conjTranspose_apply]
    rw [e2, Matrix.add_apply, e1, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < p
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
  have h1 := sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)
  rw [← key, sumBd_normSq_det, sumBd_trace_ctm] at h1
  have h2 := sumBdFsq_nonneg C
  rw [← Complex.normSq_eq_norm_sq]
  show 1 ≤ Complex.normSq A.det
  linarith
end GlobalTheory.FramePotential
