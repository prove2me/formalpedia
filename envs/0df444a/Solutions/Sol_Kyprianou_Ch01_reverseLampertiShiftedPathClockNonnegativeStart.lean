-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiShiftedPathClockNonnegativeStart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:19:26.641973+00:00
-- url     : https://prove2.me/submissions/5bf2f561-a839-4d5e-9209-b6283510d9bc

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedStoppedInverseClock
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    (compoundPoissonToBranching X t ω).toNat =
      (compoundPoissonToBranching Y
        (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω).toNat := by
  classical
  have hStop :=
    reverseLampertiShiftedStoppedInverseClock
      X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative
  have hPath (s : ℝ≥0) : X (Real.toNNReal A + s) ω = Y s ω := by
    have hBound : A ≤ (((Real.toNNReal A + s : ℝ≥0) : ℝ)) := by
      rw [NNReal.coe_add, Real.coe_toNNReal A hA]
      exact le_add_of_nonneg_right s.property
    have hEq := hShift (Real.toNNReal A + s) hBound
    simpa [NNReal.coe_add, Real.coe_toNNReal A hA] using hEq
  unfold compoundPoissonToBranching
  rw [hStop]
  cases hMin :
      min
        (inverseReciprocalOccupation Y
          (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω)
        (firstNegativePassage Y ω) with
  | top =>
      simp only [WithTop.add_top]
  | coe s =>
      change (X (Real.toNNReal A + s) ω).toNat = (Y s ω).toNat
      exact congrArg Int.toNat (hPath s)
