-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_exponential_mixture_section
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:27:22.073246+00:00
-- url     : https://prove2.me/submissions/2644a696-ec7a-4144-ad6c-677a3e0a2509

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_shift_section_density
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08.StageB
/-- Fixed-coordinate exponential section. -/
theorem solution :
    ∀ (φ x d : ℝ), 0 < φ → ∀ A : Set ℝ, MeasurableSet A →
      expMeasure φ {s : ℝ | d ≤ x ∧ x + s - d ∈ A} =
      ∫⁻ y in A, (if x-y < d ∧ d ≤ x then
        ENNReal.ofReal (φ * Real.exp (-φ * (y-x+d))) else 0) := by
  intro φ x d hφ A hA
  by_cases hd : d ≤ x
  · have he : {s : ℝ | d ≤ x ∧ x + s - d ∈ A} =
        (fun s : ℝ => s + (x-d)) ⁻¹' A := by
      ext s
      have hh : x+s-d = s+(x-d) := by ring
      simp [hd, hh]
    rw [he, p2m88_exponential_shift_section_density φ (x-d) hφ A hA]
    apply lintegral_congr
    intro y
    by_cases hy : x-y < d
    · have hy' : x-d < y := by linarith
      have hh : y-(x-d) = y-x+d := by ring
      simp [hd, hy, hy', hh]
    · have hy' : ¬ x-d < y := by linarith
      simp [hd, hy, hy']
  · simp [hd]
