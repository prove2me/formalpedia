-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_setLIntegral_Ioc_prod_zero
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:03:31.073872+00:00
-- url     : https://prove2.me/submissions/43405be1-f572-4784-9480-5095c66b68e7

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (φ : Ω → ℝ → ℝ≥0∞) (hφ : Measurable (Function.uncurry φ))
    {s₀ T : ℝ} (hs₀ : 0 ≤ s₀) (hs₀T : s₀ < T)
    (h_fin : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, φ ω u ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s₀ r, φ ω u ∂volume ∂P)
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
  have swap (s : Set ℝ) :
      (∫⁻ ω, ∫⁻ u in s, φ ω u ∂volume ∂P) = ∫⁻ u in s, ∫⁻ ω, φ ω u ∂P :=
    lintegral_lintegral_swap hφ.aemeasurable
  let g : ℝ → ℝ≥0∞ := fun u => ∫⁻ ω, φ ω u ∂P
  have hg : ∫⁻ u, (Set.Icc (0 : ℝ) T).indicator g u ≠ ⊤ := by
    rw [lintegral_indicator measurableSet_Icc]
    exact (swap _ ▸ h_fin)
  have hv : Tendsto (volume ∘ (fun r : ℝ => Set.Ioc s₀ r)) (𝓝[>] s₀) (𝓝 0) := by
    simp only [Function.comp_def, Real.volume_Ioc]
    have h : Tendsto (fun r : ℝ => r - s₀) (𝓝[>] s₀) (𝓝 (s₀ - s₀)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.sub tendsto_const_nhds)
    simpa using ENNReal.tendsto_ofReal h
  apply (tendsto_setLIntegral_zero hg hv).congr'
  have hT : ∀ᶠ r in 𝓝[>] s₀, r < T :=
    Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hs₀T)
  filter_upwards [hT] with r hr
  rw [swap, setLIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.mpr (show Set.Ioc s₀ r ⊆ Set.Icc 0 T from
      fun u hu => ⟨hs₀.trans hu.1.le, hu.2.trans hr.le⟩)]

#print axioms solution
