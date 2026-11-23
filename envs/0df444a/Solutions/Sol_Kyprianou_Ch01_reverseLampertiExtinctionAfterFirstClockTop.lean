-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiExtinctionAfterFirstClockTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:53:04.257904+00:00
-- url     : https://prove2.me/submissions/f1e0644a-2ad7-4fdc-83a0-48838880d3e0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroStageReciprocalOccupationTop
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (a b : ℝ) (ha : 0 < a) (hAB : a < b)
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hZero : y + j - 1 = 0) :
    ∀ u : ℝ≥0, a < (u : ℝ) → (u : ℝ) < b →
      reciprocalOccupation X u ω = ⊤ := by
  intro u hau hub
  have hZeroOn (v : ℝ≥0) (hav : a < (v : ℝ))
      (hvu : (v : ℝ) < (u : ℝ)) : X v ω = 0 := by
    have hXu := hMiddle v hav.le (lt_trans hvu hub)
    simpa only [hZero, Nat.cast_zero] using hXu
  have H := Kyprianou.Ch01.reverseLampertiZeroStageReciprocalOccupationTop
    X ω a (u : ℝ) ha.le hau hZeroOn
  simpa using H
