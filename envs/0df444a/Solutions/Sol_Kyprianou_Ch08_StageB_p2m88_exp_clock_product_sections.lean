-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_exp_clock_product_sections
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:04:11.659364+00:00
-- url     : https://prove2.me/submissions/c2915ac2-5b0d-4d6d-9ec6-f860da13e209

import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact source clock reduction. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (q : ℝ), 0 < q → ∀ B : Set (Ω × ℝ≥0), MeasurableSet B →
      let f : ℝ≥0 → ℝ≥0∞ := fun t => P ((fun ω : Ω => (ω, t)) ⁻¹' B)
      Measurable f ∧
        (∫⁻ r : ℝ, f r.toNNReal ∂expMeasure q) =
        (P.prod (expMeasure q)) {z : Ω × ℝ | 0 ≤ z.2 ∧ (z.1, z.2.toNNReal) ∈ B} := by
  intro Ω mΩ P hP q hq B hB
  dsimp only
  let f : ℝ≥0 → ℝ≥0∞ := fun t => P ((fun ω : Ω => (ω, t)) ⁻¹' B)
  let B' : Set (Ω × ℝ) := (fun z : Ω × ℝ => (z.1, z.2.toNNReal)) ⁻¹' B
  have hf : Measurable f := measurable_measure_prodMk_right hB
  have hB' : MeasurableSet B' :=
    (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd)) hB
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  have hexp : (expMeasure q) (Iio (0 : ℝ)) = 0 := by
    change (volume.withDensity (exponentialPDF q)) (Iio (0 : ℝ)) = 0
    rw [withDensity_apply _ measurableSet_Iio]
    exact lintegral_exponentialPDF_of_nonpos le_rfl
  have hae : ∀ᵐ r ∂expMeasure q, 0 ≤ r := by
    rw [ae_iff]
    simp only [not_le]
    change (expMeasure q) (Iio (0 : ℝ)) = 0
    exact hexp
  have hprod : ∀ᵐ z ∂P.prod (expMeasure q), 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ => hae
  refine ⟨hf, ?_⟩
  calc
    (∫⁻ r : ℝ, f r.toNNReal ∂expMeasure q) = (P.prod (expMeasure q)) B' := by
      rw [Measure.prod_apply_symm hB']
      rfl
    _ = _ := by
      apply measure_congr
      filter_upwards [hprod] with z hz
      change ((z.1, z.2.toNNReal) ∈ B) =
        (0 ≤ z.2 ∧ (z.1, z.2.toNNReal) ∈ B)
      simp [hz]
