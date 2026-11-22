-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiZeroTimePathwiseOfContinuousAtZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:51:10.352745+00:00
-- url     : https://prove2.me/submissions/bb126ef5-563b-4fba-84ad-9ddd752b00ee

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPositiveNearZeroOfRightContinuous
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationMonotone
import Theorems.Thm_Kyprianou_Ch01_extendedClockInverseBeforeHorizon
open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hNonneg : 0 ≤ X 0 ω)
    (hRight : ContinuousWithinAt
      (fun s : ℝ≥0 => X s ω) (Set.Ici 0) 0) :
    (compoundPoissonToBranching X 0 ω).toNat = (X 0 ω).toNat := by
  obtain ⟨horizon, hHorizon, hClock⟩ :=
    Kyprianou.Ch01.reciprocalOccupationPositiveNearZeroOfRightContinuous
      X ω hNonneg hRight
  have hAtZero : reciprocalOccupation X 0 ω = 0 := by
    simp [reciprocalOccupation]
  have hMonotone := Kyprianou.Ch01.reciprocalOccupationMonotone X ω
  have hInf : sInf {s : ℝ≥0 |
      reciprocalOccupation X 0 ω < reciprocalOccupation X s ω} = 0 := by
    apply Kyprianou.Ch01.extendedClockInverseBeforeHorizon
      (fun s : ℝ≥0 => reciprocalOccupation X s ω)
      hMonotone 0 horizon hHorizon
    intro s hs hsHorizon
    simpa [hAtZero] using hClock s hs hsHorizon
  obtain ⟨s, hs0, hsHorizon⟩ := exists_between hHorizon
  have hExists :
      ∃ s : ℝ≥0, (0 : ℝ≥0∞) < reciprocalOccupation X s ω :=
    ⟨s, hClock s hs0 hsHorizon⟩
  have hInverse :
      inverseReciprocalOccupation X 0 ω = (0 : WithTop ℝ≥0) := by
    unfold inverseReciprocalOccupation
    split_ifs with hCondition
    · simpa [hAtZero] using
        congrArg (fun v : ℝ≥0 => (v : WithTop ℝ≥0)) hInf
    · exact False.elim (hCondition hExists)
  simp [compoundPoissonToBranching, hInverse]
