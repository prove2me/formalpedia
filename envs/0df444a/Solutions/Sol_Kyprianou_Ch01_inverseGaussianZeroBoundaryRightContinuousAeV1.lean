-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianZeroBoundaryRightContinuousAeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:27:00.95512+00:00
-- url     : https://prove2.me/submissions/130a6f19-277a-4f69-ab7b-d1543e31c38b

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianAllPositiveLevelsFiniteAeV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianPositiveLevelPassageRightContinuousOfFiniteV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianZeroLevelPassageRightContinuousAeV1
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
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => T u ω) (Ici s) s := by
  have hFin :
      ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s →
        firstUpperPassage X (s : ℝ) ω ≠ ⊤ :=
    inverseGaussianAllPositiveLevelsFiniteAeV1 P X b hb hB hMeas
  have hZero :
      ∀ᵐ ω ∂P, ContinuousWithinAt
        (fun u : ℝ≥0 =>
          if u = 0 then (0 : ℝ)
          else (match firstUpperPassage X (u : ℝ) ω with
          | none => (0 : ℝ)
          | some t => (t : ℝ))) (Ici (0 : ℝ≥0)) 0 :=
    inverseGaussianZeroLevelPassageRightContinuousAeV1
      P X b hb hB hMeas hContinuous
  dsimp only
  filter_upwards [hFin, hZero] with ω hfin hz
  intro s
  by_cases hs : s = 0
  · subst s
    exact hz
  · have h0s : (0 : ℝ≥0) ≤ s := zero_le
    have hspos : 0 < s := lt_of_le_of_ne h0s (Ne.symm hs)
    exact inverseGaussianPositiveLevelPassageRightContinuousOfFiniteV1
      X ω hfin s hspos
