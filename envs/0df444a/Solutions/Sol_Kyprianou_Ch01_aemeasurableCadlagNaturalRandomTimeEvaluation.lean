-- Prove2me | solution 1 for Kyprianou.Ch01.aemeasurableCadlagNaturalRandomTimeEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:43:35.240075+00:00
-- url     : https://prove2.me/submissions/536569b7-13bf-461f-839c-6744e826d1ac

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch01_aemeasurableRightContinuousRealRandomTimeEvaluation
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Measurable sampling of a natural-valued càdlàg process at a random time
requires only almost-sure càdlàg paths, not universal path regularity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (T : Ω → ℝ≥0) (hT : Measurable T) :
    AEMeasurable (fun ω : Ω => (Y (T ω) ω : ℝ)) P := by
  have hCast : Continuous (fun n : ℕ => (n : ℝ)) :=
    continuous_of_discreteTopology
  have hMeasReal : ∀ t : ℝ≥0,
      Measurable (fun ω : Ω => (Y t ω : ℝ)) := by
    intro t
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (hMeas t)
  have hRightReal : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 => (Y s ω : ℝ)) (Ici t) t := by
    filter_upwards [hCadlag] with ω hω
    intro t
    exact hCast.continuousAt.comp_continuousWithinAt (hω t).1
  exact Kyprianou.Ch01.aemeasurableRightContinuousRealRandomTimeEvaluation
    P (fun t ω => (Y t ω : ℝ))
    hMeasReal hRightReal T hT
