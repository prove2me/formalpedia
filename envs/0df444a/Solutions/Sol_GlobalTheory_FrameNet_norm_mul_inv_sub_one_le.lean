-- Prove2me | solution 1 for GlobalTheory.FrameNet.norm_mul_inv_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:42.958257+00:00
-- url     : https://prove2.me/submissions/baee8428-d170-4d89-ad9c-d093c92d9455

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
import Theorems.Thm_GlobalTheory_FrameNet_norm_det_le
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
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
namespace GlobalTheory.FrameNet
theorem _root_.solution {r : ℕ} {m m' : Matrix (Fin r) (Fin r) ℂ} {s ε : ℝ} (hs : 1 ≤ s)
    (hm : ∀ i k, ‖m' i k‖ ≤ s) (hd : m'.det ≠ 0) (hε : ∀ i k, ‖m i k - m' i k‖ ≤ ε) (a b : Fin r) :
    ‖(m * m'⁻¹) a b - (if a = b then 1 else 0)‖ ≤ r * (ε * ((r : ℝ) ^ r * s ^ r / ‖m'.det‖)) := by
  have hu : IsUnit m'.det := isUnit_iff_ne_zero.mpr hd
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε a a)
  have hadj : ∀ k c, ‖m'.adjugate k c‖ ≤ (r : ℝ) ^ r * s ^ r := by
    intro k c
    rw [Matrix.adjugate_apply]
    apply norm_det_le (by linarith)
    intro i j
    rw [Matrix.updateRow_apply]
    split_ifs with h
    · by_cases hjk : j = k <;> simp [hjk] <;> linarith
    · exact hm i j
  have hinv : ∀ k c, ‖m'⁻¹ k c‖ ≤ (r : ℝ) ^ r * s ^ r / ‖m'.det‖ := by
    intro k c
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, norm_mul, norm_inv,
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hadj k c) (inv_nonneg.mpr (norm_nonneg _))
  have hkey : (m * m'⁻¹) a b - (if a = b then 1 else 0) = ∑ k, (m a k - m' a k) * m'⁻¹ k b := by
    have h1 : m * m'⁻¹ - 1 = (m - m') * m'⁻¹ := by rw [sub_mul, Matrix.mul_nonsing_inv _ hu]
    have h2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, Matrix.one_apply] at h2
    rw [h2, Matrix.mul_apply]
    simp only [Matrix.sub_apply]
  rw [hkey]
  calc ‖∑ k, (m a k - m' a k) * m'⁻¹ k b‖ ≤ ∑ k, ‖(m a k - m' a k) * m'⁻¹ k b‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin r, ε * ((r : ℝ) ^ r * s ^ r / ‖m'.det‖) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hε a k) (hinv k b) (norm_nonneg _) hε0
    _ = r * (ε * ((r : ℝ) ^ r * s ^ r / ‖m'.det‖)) := by simp
end GlobalTheory.FrameNet
