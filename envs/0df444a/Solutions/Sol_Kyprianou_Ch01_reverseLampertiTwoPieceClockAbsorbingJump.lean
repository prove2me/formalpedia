-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoPieceClockAbsorbingJump
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:32:26.985038+00:00
-- url     : https://prove2.me/submissions/74ac6b15-d2ae-45a0-9639-2d88a35cf726
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassageAfterNonnegativeOpenInterval
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceInverseClockAtExtinction
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
    (compoundPoissonToBranching X t ω).toNat = y + j - 1 := by
  let c : ℝ≥0 := Real.toNNReal a
  have hc : (c : ℝ) = a := Real.coe_toNNReal a ha.le
  have hNonneg (u : ℝ≥0) (hu : u < c) : 0 ≤ X u ω := by
    have huA : (u : ℝ) < a := by
      calc (u : ℝ) < (c : ℝ) := NNReal.coe_lt_coe.mpr hu
        _ = a := hc
    rw [hPrefix u huA]
    exact Int.natCast_nonneg y
  have hPassage :=
    Kyprianou.Ch01.firstNegativePassageAfterNonnegativeOpenInterval
      X ω c hNonneg
  have hTheta :=
    Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockAtExtinction
      X ω y j hy t a b ha hAB hPrefix hMiddle hZero hFirst hSecond
  have hState :
      X c ω = ((y + j - 1 : ℕ) : ℤ) :=
    hMiddle c (by rw [hc]) (by rw [hc]; exact hAB)
  have hMin : min (inverseReciprocalOccupation X t ω)
      (firstNegativePassage X ω) = (c : WithTop ℝ≥0) := by
    rw [hTheta]
    exact min_eq_left hPassage
  simp [compoundPoissonToBranching, hMin, hState]
