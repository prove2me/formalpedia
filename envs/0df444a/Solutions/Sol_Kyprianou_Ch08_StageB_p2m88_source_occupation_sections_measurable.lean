-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_source_occupation_sections_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:44:24.787368+00:00
-- url     : https://prove2.me/submissions/fcf8ce61-7b25-4d32-9df2-b3e13e5d38da

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_section_to_strict_event
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Measurability of source killed occupation time sections. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      ∀ x : ℝ, 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      Measurable (fun t : ℝ≥0 =>
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          shifted D.X x t ω ∈ A}) := by
  intro Ω mΩ P hP D ψ hψ x hx A hA
  obtain ⟨F, X, hpath, _⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hm := (p2m88_avram_clock_section_to_strict_event Ω P F X 1 x zero_lt_one hx A hA).1
  have he : (fun t : ℝ≥0 =>
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
        shifted D.X x t ω ∈ A}) =
      fun t : ℝ≥0 =>
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted X.X x) 0 ω ∧
        shifted X.X x t ω ∈ A} := by
    funext t
    apply measure_congr
    filter_upwards [hpath] with ω hω
    change ((t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
      shifted D.X x t ω ∈ A) =
      ((t : WithTop ℝ≥0) < tauMinus (shifted X.X x) 0 ω ∧
        shifted X.X x t ω ∈ A)
    simp only [tauMinus, shifted, hω]
  rw [he]
  exact hm
