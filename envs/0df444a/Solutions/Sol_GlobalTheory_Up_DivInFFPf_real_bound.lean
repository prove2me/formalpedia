-- Prove2me | solution 1 for GlobalTheory.Up.DivInFFPf.real_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:42.127941+00:00
-- url     : https://prove2.me/submissions/840559fd-834c-4551-88ac-d9e8d0246f02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralFundSetInterLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOpenSaturation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
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
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.DivInFFPf
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa)
namespace GlobalTheory.Up.DivInFFPf
theorem _root_.solution {e F G w s K C : ℝ} {a b : ℂ} {n : ℕ} (hn : 1 ≤ n) (he : 0 ≤ e) (hF : F = e * ‖a‖ ^ 2)
    (hG : G = e * ‖b‖ ^ 2) (hw : 0 < w) (hs : 0 ≤ s) (hK : w ≤ K * s) (hC : G ≤ C * w ^ n) :
    e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2)) ≤
      2 * |K| ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) + 2 * |K| ^ ((n : ℝ) - 1 / 2) * C := by
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hKs : 0 < K * s := hw.trans_le hK
  have hs' : 0 < s := lt_of_le_of_ne hs (by rintro rfl; simp at hKs)
  have hK0 : 0 < K := (mul_pos_iff_of_pos_right hs').1 hKs
  rw [abs_of_pos hK0]
  have h1 : s ^ (-((n : ℝ) - 1 / 2)) ≤ K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2)) := by
    have : (K * s) ^ (-((n : ℝ) - 1 / 2)) ≤ w ^ (-((n : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hw hK (by linarith)
    rw [Real.mul_rpow hK0.le hs, Real.rpow_neg hK0.le,
      inv_mul_le_iff₀ (Real.rpow_pos_of_pos hK0 _)] at this
    exact this
  have h2 : w ^ (-(1 / 2 : ℝ)) * w ^ (-((n : ℝ) - 1 / 2)) = w ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add hw]; congr 1; ring
  have h3 : e * ‖a - b‖ ^ 2 ≤ 2 * F + 2 * G := by
    have h4 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [hF, hG]
    nlinarith [mul_le_mul_of_nonneg_left h4 he]
  have h5 : G * w ^ (-(n : ℝ)) ≤ C := by
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, mul_inv_le_iff₀ (pow_pos hw n)]
    exact hC
  have hKp := Real.rpow_pos_of_pos hK0 ((n : ℝ) - 1 / 2)
  calc e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2))
      ≤ (2 * F + 2 * G) * w ^ (-(1 / 2 : ℝ)) * (K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2))) := by
        have : 0 ≤ 2 * F + 2 * G := le_trans (by positivity) h3
        gcongr
    _ = 2 * K ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) +
          2 * K ^ ((n : ℝ) - 1 / 2) * (G * w ^ (-(n : ℝ))) := by rw [← h2]; ring
    _ ≤ _ := by gcongr
end GlobalTheory.Up.DivInFFPf
