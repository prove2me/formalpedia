-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_avram_clock_survival_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:59:34.61538+00:00
-- url     : https://prove2.me/submissions/3a8aff4b-48ea-444c-a1ef-0470133fc7c2

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exp_clock_normalization
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_section_to_strict_event
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_strict_event_to_infimum
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact clock calculation. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ (q x : ℝ), 0 < q → 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          tauMinus (shifted X.X x) 0 ω ∧ shifted X.X x t ω ∈ A}
          ∂positiveTimeLebesgue) =
      (ENNReal.ofReal q)⁻¹ * (P.prod (expMeasure q))
        {z : Ω × ℝ | (-sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1}) ≤ x ∧
          x + X.X z.2.toNNReal z.1 ∈ A} := by
  intro Ω mΩ P hP F X q x hq hx A hA
  let f : ℝ≥0 → ℝ≥0∞ := fun t =>
    P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted X.X x) 0 ω ∧
      shifted X.X x t ω ∈ A}
  obtain ⟨hf, hs⟩ :=
    p2m88_avram_clock_section_to_strict_event Ω P F X q x hq hx A hA
  change (∫⁻ t, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) * f t
    ∂positiveTimeLebesgue) = _
  rw [p2m88_exp_clock_normalization q hq f hf, hs,
    p2m88_avram_clock_strict_event_to_infimum Ω P F X q x hq hx A hA]
