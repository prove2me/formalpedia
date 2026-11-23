-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiTwoPieceClockPositiveJump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:32:38.095947+00:00
-- url     : https://prove2.me/submissions/a810ca13-0006-4506-934a-96b9f67de282

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassageAfterNonnegativeOpenInterval
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceInverseClockInsidePositiveStage
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
    (hPost : 0 < y + j - 1)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    (compoundPoissonToBranching X t ω).toNat = y + j - 1 := by
  obtain ⟨s, hsLower, hsUpper, hTheta⟩ :=
    Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockInsidePositiveStage
      X ω y j hy t a b ha hAB hPrefix hMiddle hPost hFirst hSecond
  let c : ℝ≥0 := Real.toNNReal b
  have hb : 0 < b := lt_trans ha hAB
  have hc : (c : ℝ) = b := Real.coe_toNNReal b hb.le
  have hNonneg (u : ℝ≥0) (hu : u < c) : 0 ≤ X u ω := by
    have huB : (u : ℝ) < b := by
      calc (u : ℝ) < (c : ℝ) := NNReal.coe_lt_coe.mpr hu
        _ = b := hc
    by_cases huA : (u : ℝ) < a
    · rw [hPrefix u huA]
      exact Int.natCast_nonneg y
    · rw [hMiddle u (le_of_not_gt huA) huB]
      exact Int.natCast_nonneg _
  have hPassB :=
    Kyprianou.Ch01.firstNegativePassageAfterNonnegativeOpenInterval
      X ω c hNonneg
  have hsC : s ≤ c := by
    apply le_of_lt
    apply NNReal.coe_lt_coe.mp
    simpa only [hc] using hsUpper
  have hPassS : (s : WithTop ℝ≥0) ≤ firstNegativePassage X ω :=
    (WithTop.coe_le_coe.mpr hsC).trans hPassB
  have hState : X s ω = ((y + j - 1 : ℕ) : ℤ) :=
    hMiddle s hsLower hsUpper
  have hMin : min (inverseReciprocalOccupation X t ω)
      (firstNegativePassage X ω) = (s : WithTop ℝ≥0) := by
    rw [hTheta]
    exact min_eq_left hPassS
  simp [compoundPoissonToBranching, hMin, hState]
