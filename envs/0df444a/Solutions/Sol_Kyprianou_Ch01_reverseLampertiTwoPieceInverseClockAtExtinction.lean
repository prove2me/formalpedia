-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockAtExtinction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:52:08.202393+00:00
-- url     : https://prove2.me/submissions/f100b7fc-e3c5-4e56-bbc6-f5f6b7b9c901

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiExtinctionBeforeFirstClockBound
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiExtinctionAfterFirstClockTop
import Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationBoundaryFromClockBounds
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hZero : y + j - 1 = 0)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    inverseReciprocalOccupation X t ω = (Real.toNNReal a : WithTop ℝ≥0) := by
  have hb0 : 0 ≤ b := le_trans ha.le hAB.le
  have hABNN : Real.toNNReal a < Real.toNNReal b := by
    apply NNReal.coe_lt_coe.mp
    simpa only [Real.coe_toNNReal a ha.le,
      Real.coe_toNNReal b hb0] using hAB
  apply Kyprianou.Ch01.inverseReciprocalOccupationBoundaryFromClockBounds
    X ω t (Real.toNNReal a) (Real.toNNReal b) hABNN
  · intro u hu
    have huR : (u : ℝ) < a := by
      have h := NNReal.coe_lt_coe.mpr hu
      simpa only [Real.coe_toNNReal a ha.le] using h
    exact Kyprianou.Ch01.reverseLampertiExtinctionBeforeFirstClockBound
      X ω y hy t a ha hPrefix hFirst u huR
  · intro u hua hub
    have huaR : a < (u : ℝ) := by
      have h := NNReal.coe_lt_coe.mpr hua
      simpa only [Real.coe_toNNReal a ha.le] using h
    have hubR : (u : ℝ) < b := by
      have h := NNReal.coe_lt_coe.mpr hub
      simpa only [Real.coe_toNNReal b hb0] using h
    exact Kyprianou.Ch01.reverseLampertiExtinctionAfterFirstClockTop
      X ω y j a b ha hAB hMiddle hZero u huaR hubR
