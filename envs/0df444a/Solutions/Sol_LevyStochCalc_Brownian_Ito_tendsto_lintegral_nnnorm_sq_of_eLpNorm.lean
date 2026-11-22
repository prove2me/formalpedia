-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:03:29.137778+00:00
-- url     : https://prove2.me/submissions/10a518d3-7758-43da-9324-679aa495a319

import Mathlib

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {β : Type*} [MeasurableSpace β] {μ : MeasureTheory.Measure β}
    {ι : Type*} {l : Filter ι} {gₙ : ι → β → ℝ} {g : β → ℝ}
    (hgₙ : ∀ n, MeasureTheory.AEStronglyMeasurable (gₙ n) μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ)
    (hgfin : MeasureTheory.eLpNorm g 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x, (‖gₙ n x‖₊ : ℝ≥0∞) ^ 2 ∂μ) l
      (nhds (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ)) := by
  have hN : Tendsto (fun n => eLpNorm (gₙ n) 2 μ) l (𝓝 (eLpNorm g 2 μ)) := by
    have hconst : Tendsto (fun _ : ι => eLpNorm g 2 μ) l (𝓝 (eLpNorm g 2 μ)) := tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [tsub_zero] using ENNReal.Tendsto.sub hconst htend (Or.inl hgfin))
      (by simpa only [zero_add] using htend.add hconst)
    · intro n
      apply tsub_le_iff_right.mpr
      simpa only [sub_sub_cancel] using
        (eLpNorm_sub_le (hgₙ n) ((hgₙ n).sub hg) (μ := μ) (p := 2) (by norm_num))
    · intro n
      simpa only [sub_add_cancel] using
        (eLpNorm_add_le ((hgₙ n).sub hg) hg (μ := μ) (p := 2) (by norm_num))
  have hsq (f : β → ℝ) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    simpa [enorm_eq_nnnorm, ENNReal.rpow_two] using (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) (by norm_num))
  simpa only [← hsq] using (ENNReal.Tendsto.pow (n := 2) hN)
