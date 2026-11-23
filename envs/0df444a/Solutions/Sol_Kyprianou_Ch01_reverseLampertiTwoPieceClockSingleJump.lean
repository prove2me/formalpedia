-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoPieceClockSingleJump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:20:33.940973+00:00
-- url     : https://prove2.me/submissions/ed29d2ef-99ac-4c37-84ea-e9c504ee9b03

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceClockAbsorbingJump
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceClockPositiveJump
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
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    (compoundPoissonToBranching X t ω).toNat = y + j - 1 := by
  by_cases hz : y + j - 1 = 0
  · exact Kyprianou.Ch01.reverseLampertiTwoPieceClockAbsorbingJump
      X ω y j hy t a b ha hAB hPrefix hMiddle hz hFirst hSecond
  · have hPos : 0 < y + j - 1 := Nat.pos_of_ne_zero hz
    exact Kyprianou.Ch01.reverseLampertiTwoPieceClockPositiveJump
      X ω y j hy t a b ha hAB hPrefix hMiddle hPos hFirst hSecond
