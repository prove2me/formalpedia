-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianZeroBoundaryCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:19:03.909183+00:00
-- url     : https://prove2.me/submissions/1d75d75a-23ba-419a-9950-6ef29b2c3a8f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianAllPositiveLevelsFiniteAeV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroBoundaryRightContinuousAeV1
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => T t ω) := by
  have hFinite :
      ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s →
        firstUpperPassage X (s : ℝ) ω ≠ ⊤ :=
    inverseGaussianAllPositiveLevelsFiniteAeV1 P X b hb hB hMeas
  have hRC :
      ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
        ContinuousWithinAt
          (fun u : ℝ≥0 =>
            if u = 0 then (0 : ℝ)
            else (match firstUpperPassage X (u : ℝ) ω with
            | none => (0 : ℝ)
            | some v => (v : ℝ))) (Ici s) s :=
    inverseGaussianZeroBoundaryRightContinuousAeV1
      P X b hb hB hMeas hContinuous
  filter_upwards [hFinite, hRC] with ω hFin hRight
  have hMono :
      Monotone (fun s : ℝ≥0 =>
        if s = 0 then (0 : ℝ)
        else (match firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))) :=
    inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1 X ω hFin
  intro t
  exact ⟨hRight t, ⟨Function.leftLim _ t, hMono.tendsto_leftLim t⟩⟩
