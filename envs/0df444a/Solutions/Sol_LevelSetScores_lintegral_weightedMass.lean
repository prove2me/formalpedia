-- Prove2me | solution 1 for LevelSetScores.lintegral_weightedMass
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:35:06.605809+00:00
-- url     : https://prove2.me/submissions/5c6f1154-61c9-443f-9ebf-63d9a9e1f7c1

import Mathlib
import Definitions.Def_LevelSetScores_weightedMass

open MeasureTheory
open scoped ENNReal

open LevelSetScores in
theorem solution {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh_meas : Measurable h)
    {ν : Measure (EuclideanSpace ℝ (Fin d))} [SFinite ν]
    {P : Measure (EuclideanSpace ℝ (Fin d))}
    {Ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hΞ_meas : Measurable Ξ)
    (hΞ : Measure.conv P ν = volume.withDensity (fun z => ENNReal.ofReal (Ξ z)))
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    ∫⁻ y, weightedMass h ν B y ∂P =
      ∫⁻ z in B, ENNReal.ofReal (h z) * ENNReal.ofReal (Ξ z) := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := B.indicator (fun z => ENNReal.ofReal (h z)) with hF
  have hFm : Measurable F := (ENNReal.measurable_ofReal.comp hh_meas).indicator hB
  have hadd : Measurable (fun x : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      x.1 + x.2) := measurable_fst.add measurable_snd
  calc ∫⁻ y, weightedMass h ν B y ∂P = ∫⁻ x, F (x.1 + x.2) ∂(P.prod ν) := by
        rw [lintegral_prod (fun x => F (x.1 + x.2)) (hFm.comp hadd).aemeasurable]; rfl
    _ = ∫⁻ z, F z ∂(Measure.conv P ν) := by
        rw [Measure.conv, lintegral_map hFm hadd]
    _ = ∫⁻ z, ENNReal.ofReal (Ξ z) * F z := by
        rw [hΞ]
        exact lintegral_withDensity_eq_lintegral_mul volume
          (ENNReal.measurable_ofReal.comp hΞ_meas) hFm
    _ = _ := by
        rw [← lintegral_indicator hB]
        congr 1
        funext z
        by_cases hz : z ∈ B <;> simp [hF, hz, mul_comm]
