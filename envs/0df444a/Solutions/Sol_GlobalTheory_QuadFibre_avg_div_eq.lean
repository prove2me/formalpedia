-- Prove2me | solution 1 for GlobalTheory.QuadFibre.avg_div_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:56.702238+00:00
-- url     : https://prove2.me/submissions/d5261ef0-a715-4b50-8703-4197a8247eac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HaarDisintegrationAveragedFibreMeasures
import Theorems.Thm_GlobalTheory_QuadFibre_exists_map_div_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise ENNReal NNReal
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
theorem _root_.solution {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsAddHaarMeasure] {a : K} (ha : a ≠ 0)
    {U : Set K} (hU : MeasurableSet U) {g : K → ℝ≥0∞} (hg : Measurable g) :
    (ν {r | r / a ∈ U})⁻¹ * ∫⁻ t, g (t / a) ∂ν = (ν U)⁻¹ * ∫⁻ u, g u ∂ν := by
  obtain ⟨c, hc0, hc⟩ := exists_map_div_eq_smul ν ha
  have hf : Measurable (fun t : K => t / a) := (continuous_id.div_const a).measurable
  have hcU : ν {r | r / a ∈ U} = c * ν U := by
    have h : (Measure.map (fun t : K => t / a) ν) U = (c • ν) U := by rw [hc]
    rwa [Measure.map_apply hf hU, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcI : ∫⁻ t, g (t / a) ∂ν = c * ∫⁻ u, g u ∂ν := by
    rw [← lintegral_map hg hf, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hc0' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcc : (c : ℝ≥0∞)⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0' ENNReal.coe_ne_top
  rw [hcU, hcI, ENNReal.mul_inv (Or.inl hc0') (Or.inl ENNReal.coe_ne_top)]
  calc (c : ℝ≥0∞)⁻¹ * (ν U)⁻¹ * (c * ∫⁻ u, g u ∂ν)
      = (ν U)⁻¹ * (∫⁻ u, g u ∂ν) * ((c : ℝ≥0∞)⁻¹ * c) := by ring
    _ = (ν U)⁻¹ * ∫⁻ u, g u ∂ν := by rw [hcc, mul_one]
end GlobalTheory.QuadFibre
