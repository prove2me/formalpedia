-- Prove2me | solution 1 for GlobalTheory.PointSup.lintegral_le_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:59.605799+00:00
-- url     : https://prove2.me/submissions/5add6f95-b293-4f41-bc1d-c9afb5b6fe7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeDensity
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.PointSup
namespace GlobalTheory.PointSup
theorem _root_.solution {n : ℕ} {B O : Set (V n)} (hB : MeasurableSet B) (hBO : B ⊆ O)
    {d : V n → ℝ} {c : ℝ} (hc : 0 < c) (hd : ∀ z ∈ B, c ≤ d z) (g : V n → ℝ≥0∞) :
    ∫⁻ z in B, g z ≤ (ENNReal.ofReal c)⁻¹ *
      ∫⁻ z, g z ∂((volume.restrict O).withDensity fun z => ENNReal.ofReal (d z)) := by

  have hμ : ENNReal.ofReal c • volume.restrict B ≤
      (volume.restrict O).withDensity fun z => ENNReal.ofReal (d z) := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.smul_apply, Measure.restrict_apply hs, withDensity_apply _ hs,
      Measure.restrict_restrict hs, smul_eq_mul]
    calc ENNReal.ofReal c * volume (s ∩ B) = ∫⁻ _ in s ∩ B, ENNReal.ofReal c :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in s ∩ B, ENNReal.ofReal (d z) :=
          setLIntegral_mono' (hs.inter hB) fun z hz => ENNReal.ofReal_le_ofReal (hd z hz.2)
      _ ≤ ∫⁻ z in s ∩ O, ENNReal.ofReal (d z) :=
          lintegral_mono_set (Set.inter_subset_inter_right s hBO)
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  calc ∫⁻ z in B, g z = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * ∫⁻ z in B, g z) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
    _ = (ENNReal.ofReal c)⁻¹ * ∫⁻ z, g z ∂(ENNReal.ofReal c • volume.restrict B) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by gcongr
end GlobalTheory.PointSup
