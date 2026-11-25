-- Prove2me | solution 1 for GlobalTheory.PointSup.mean_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:03.145498+00:00
-- url     : https://prove2.me/submissions/591457f3-164d-4d16-a7f3-35d33f67d42b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeDensity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mv
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
theorem _root_.solution {n : ℕ} {R : ℝ} {u : V n → ℂ} (hu : DifferentiableOn ℂ u (Metric.ball 0 R))
    {g : V n → ℝ≥0∞} (hg : Measurable g) {J A : ℝ≥0∞} (hJ : J < ⊤)
    (hgJ : ∫⁻ z in Metric.ball (0 : V n) R, g z ≤ J)
    (hpt : ∀ z ∈ Metric.ball (0 : V n) R, g z < ⊤ → ENNReal.ofReal (‖u z‖ ^ 2) ≤ g z * A) :
    ENNReal.ofReal ‖u 0‖ ^ 2 * volume (Metric.ball (0 : V n) R) ≤ J * A := by
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv n 0 R u (fun _ => 1) hu measurable_const
  simp only [mul_one, setLIntegral_one] at hmv

  have hfin : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : V n) R)), g z < ⊤ :=
    ae_lt_top hg (hgJ.trans_lt hJ).ne
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : V n) R)), ‖u z‖ₑ ^ 2 ≤ g z * A := by
    filter_upwards [hfin, ae_restrict_mem measurableSet_ball] with z hz hzb
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact hpt z hzb hz
  calc ENNReal.ofReal ‖u 0‖ ^ 2 * volume (Metric.ball (0 : V n) R)
      = ‖u 0‖ₑ ^ 2 * volume (Metric.ball (0 : V n) R) := by rw [ofReal_norm]
    _ ≤ ∫⁻ z in Metric.ball (0 : V n) R, ‖u z‖ₑ ^ 2 := hmv
    _ ≤ ∫⁻ z in Metric.ball (0 : V n) R, g z * A := lintegral_mono_ae hae
    _ = (∫⁻ z in Metric.ball (0 : V n) R, g z) * A := lintegral_mul_const A hg
    _ ≤ J * A := by gcongr
end GlobalTheory.PointSup
