-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_exponential_shift_section_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:15:30.886799+00:00
-- url     : https://prove2.me/submissions/dc077888-e378-43e6-8260-b4fc092e574a

import Mathlib.MeasureTheory.Group.LIntegral
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact exponential-measure translation. -/
theorem solution :
    ∀ (φ c : ℝ), 0 < φ → ∀ A : Set ℝ, MeasurableSet A →
      (expMeasure φ) ((fun s : ℝ => s + c) ⁻¹' A) =
        ∫⁻ y in A, (Ioi c).indicator
          (fun y => ENNReal.ofReal (φ * Real.exp (-φ * (y - c)))) y := by
  intro φ c hφ A hA
  classical
  let B := (fun s : ℝ => s + c) ⁻¹' A
  have hB : MeasurableSet B := (measurable_id.add measurable_const) hA
  let g : ℝ → ℝ≥0∞ := (Ioi c).indicator
    (fun y => ENNReal.ofReal (φ * Real.exp (-φ * (y - c))))
  let F : ℝ → ℝ≥0∞ := A.indicator g
  change (volume.withDensity (exponentialPDF φ)) B = ∫⁻ y in A, g y
  rw [withDensity_apply _ hB, ← lintegral_indicator hB, ← lintegral_indicator hA]
  calc
    _ = ∫⁻ s : ℝ, F (s + c) := by
      apply lintegral_congr_ae
      filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with s hs
      have hsub : s + c - c = s := by ring
      by_cases ha : s + c ∈ A
      · have hBs : s ∈ B := ha
        by_cases hp : 0 < s
        · have hlt : c < s + c := by linarith
          simp [F, g, hBs, ha, hlt, hsub, exponentialPDF_of_nonneg hp.le]
        · have hn : s < 0 := lt_of_le_of_ne (le_of_not_gt hp) hs
          have hlt : ¬ c < s + c := by linarith
          simp [F, g, hBs, ha, hlt, hsub, exponentialPDF_of_neg hn]
      · have hBs : s ∉ B := ha
        simp [F, hBs, ha]
    _ = ∫⁻ y : ℝ, F y := lintegral_add_right_eq_self F c
    _ = _ := rfl
