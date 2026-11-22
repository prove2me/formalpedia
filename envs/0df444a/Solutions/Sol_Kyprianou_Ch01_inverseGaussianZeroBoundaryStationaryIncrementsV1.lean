-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianZeroBoundaryStationaryIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:57:28.539269+00:00
-- url     : https://prove2.me/submissions/1e7f409d-343c-4d83-b219-cadd1b6e9a3e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageClockMeasurableV1
import Theorems.Thm_Kyprianou_Ch01_stationaryIncrementsOfPositivePairsV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianPositiveBarrierStationaryIncrementV1
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
open scoped Classical
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
    ProbabilityTheory.HasStationaryIncrements T P  := by
  let T : ℝ≥0 → Ω → ℝ :=
    fun s ω =>
      if s = 0 then (0 : ℝ)
      else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ))
  change HasStationaryIncrements T P
  have hMeasT : ∀ s : ℝ≥0, AEMeasurable (T s) P := by
    intro s
    exact (Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1
      X hMeas hContinuous s).aemeasurable
  have hPos :
      ∀ (s h : ℝ≥0), 0 < s → 0 < h →
      IdentDistrib (increment T s (s + h))
        (increment T 0 h) P P := by
    intro s h hs hh
    exact inverseGaussianPositiveBarrierStationaryIncrementV1
      P X b hb hB hMeas hContinuous s h hs hh
  exact stationaryIncrementsOfPositivePairsV1 P T hMeasT hPos
