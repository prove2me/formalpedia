-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_exp_clock_normalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:03:07.793208+00:00
-- url     : https://prove2.me/submissions/3473e57c-22f6-4ef7-acdc-90d268eed5b4

import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact clock calculation. -/
theorem solution :
    ∀ q : ℝ, 0 < q → ∀ f : ℝ≥0 → ℝ≥0∞, Measurable f →
      (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) * f t
        ∂positiveTimeLebesgue) =
      (ENNReal.ofReal q)⁻¹ * ∫⁻ r : ℝ, f r.toNNReal ∂expMeasure q := by
  intro q hq f hf
  let g : ℝ≥0 → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.exp (-q * (t : ℝ))) * f t
  let k : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (Real.exp (-(q * r))) * f r.toNNReal
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hk : Measurable k := by dsimp [k]; fun_prop
  have hf' : Measurable (fun r : ℝ => f r.toNNReal) := hf.comp measurable_real_toNNReal
  have hpdf : Measurable (exponentialPDF q) :=
    (measurable_exponentialPDFReal q).ennreal_ofReal
  have hpdfmul : exponentialPDF q * (fun r => f r.toNNReal) =
      (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal q * k r) := by
    funext r
    by_cases hr : 0 ≤ r
    · simp only [Pi.mul_apply, Set.indicator_of_mem (Set.mem_Ici.mpr hr),
        exponentialPDF_of_nonneg hr, ENNReal.ofReal_mul hq.le, k, mul_assoc]
    · simp [Pi.mul_apply, exponentialPDF_of_neg (lt_of_not_ge hr), hr]
  change (∫⁻ t, g t ∂positiveTimeLebesgue) =
    (ENNReal.ofReal q)⁻¹ * ∫⁻ r, f r.toNNReal ∂expMeasure q
  rw [positiveTimeLebesgue, lintegral_map hg measurable_real_toNNReal]
  change (∫⁻ r in Ici (0 : ℝ), g r.toNNReal) =
    (ENNReal.ofReal q)⁻¹ *
      ∫⁻ r, f r.toNNReal ∂(volume.withDensity (exponentialPDF q))
  rw [lintegral_withDensity_eq_lintegral_mul _ hpdf hf', hpdfmul,
    lintegral_indicator measurableSet_Ici, lintegral_const_mul _ hk, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp [hq]) ENNReal.ofReal_ne_top, one_mul]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
  simp only [g, k, Real.coe_toNNReal _ hr, neg_mul]
