-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_killed_two_sided_occupation_sections_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T03:11:46.672809+00:00
-- url     : https://prove2.me/submissions/b4dc50d8-b934-4544-978c-5fd86a411b44

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_avram_two_sided_occupation_sections_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
/-- Measurability of the two-sided killed occupation time sections. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    ∀ (A : Set ℝ), MeasurableSet A →
    Measurable (fun t : ℝ≥0 =>
      P {ω | (t : WithTop ℝ≥0) <
        min (tauMinus (shifted D.X x) 0 ω)
          (tauPlus (shifted D.X x) a ω) ∧
        shifted D.X x t ω ∈ A}) := by
  intro Ω mΩ P hP D ψ hψ a x ha hx hxa A hA
  obtain ⟨F, X, hpath, _⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hAvram := qzero_avram_two_sided_occupation_sections_measurable
    Ω P F X a x ha hx hxa A hA
  have he :
      (fun t : ℝ≥0 =>
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus (shifted D.X x) 0 ω)
            (tauPlus (shifted D.X x) a ω) ∧
          shifted D.X x t ω ∈ A}) =
      fun t : ℝ≥0 =>
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus (shifted X.X x) 0 ω)
            (tauPlus (shifted X.X x) a ω) ∧
          shifted X.X x t ω ∈ A} := by
    funext t
    apply measure_congr
    filter_upwards [hpath] with ω hω
    change (((t : ℝ≥0∞) <
        min ((tauMinus (shifted D.X x) 0 ω : ℝ≥0∞))
          ((tauPlus (shifted D.X x) a ω : ℝ≥0∞)) ∧
        x + D.X t ω ∈ A) =
      ((t : ℝ≥0∞) <
        min ((tauMinus (shifted X.X x) 0 ω : ℝ≥0∞))
          ((tauPlus (shifted X.X x) a ω : ℝ≥0∞)) ∧
        x + X.X t ω ∈ A))
    simp only [tauMinus, tauPlus, shifted, hω]
  rw [he]
  exact hAvram
