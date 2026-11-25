-- Prove2me | solution 1 for GlobalTheory.PointSup.point_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:36.434903+00:00
-- url     : https://prove2.me/submissions/021bb7e6-e6c4-481d-9d41-ad7f636b3346

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeDensity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.PointSup
namespace GlobalTheory.PointSup
theorem _root_.solution {p k K e c : ℝ} {w S : ℝ≥0∞} (hk : 0 < k) (hkK : k ≤ K) (hc : 0 < c) (hce : c ≤ e)
    (hw : w ≠ 0) (hS : (ENNReal.ofReal e / w) ^ (1 / 2 : ℝ) ≤ S)
    (hfin : ENNReal.ofReal p * w * ENNReal.ofReal k⁻¹ < ⊤) :
    ENNReal.ofReal p ≤
      ENNReal.ofReal p * w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2) := by
  rcases le_or_gt p 0 with hp | hp
  · simp [ENNReal.ofReal_of_nonpos hp]
  have hK : 0 < K := hk.trans_le hkK
  have hwt : w ≠ ⊤ := by
    rintro rfl
    have h1 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
    have h2 : ENNReal.ofReal k⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hk)).ne'
    rw [ENNReal.mul_top h1, ENNReal.top_mul h2] at hfin
    exact lt_irrefl _ hfin

  have hS2 : ENNReal.ofReal e / w ≤ S ^ 2 := by
    have h := ENNReal.pow_le_pow_left (n := 2) hS
    have h' : ((ENNReal.ofReal e / w) ^ (1 / 2 : ℝ)) ^ 2 = ENNReal.ofReal e / w := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    rwa [h'] at h
  have he : ENNReal.ofReal e ≤ S ^ 2 * w := (ENNReal.div_le_iff hw hwt).1 hS2
  have hreal : 1 ≤ k⁻¹ * (K / c) * e := by
    have h1 : 1 ≤ K / k := by rw [le_div_iff₀ hk]; linarith
    have h2 : 1 ≤ e / c := by rw [le_div_iff₀ hc]; linarith
    have h3 : k⁻¹ * (K / c) * e = (K / k) * (e / c) := by simp only [div_eq_mul_inv]; ring
    rw [h3]; nlinarith

  have hone : 1 ≤ w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2) := by
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (k⁻¹ * (K / c) * e) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal k⁻¹ * ENNReal.ofReal (K / c) * ENNReal.ofReal e := by
          rw [ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hk.le) (div_nonneg hK.le hc.le)),
            ENNReal.ofReal_mul (inv_nonneg.2 hk.le)]
      _ ≤ ENNReal.ofReal k⁻¹ * ENNReal.ofReal (K / c) * (S ^ 2 * w) := by gcongr
      _ = w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2) := by ring
  calc ENNReal.ofReal p = ENNReal.ofReal p * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal p * (w * ENNReal.ofReal k⁻¹ * (ENNReal.ofReal (K / c) * S ^ 2)) := by gcongr
    _ = _ := by ring
end GlobalTheory.PointSup
