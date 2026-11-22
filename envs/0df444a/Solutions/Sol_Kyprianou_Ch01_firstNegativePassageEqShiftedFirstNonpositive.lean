-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassageEqShiftedFirstNonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:09:30.65705+00:00
-- url     : https://prove2.me/submissions/d396975b-7a24-40f5-a723-58eac76b6eb9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- For a nonnegative initial integer state, strict-negative passage
coincides exactly with nonpositive passage of the path shifted by one. -/
theorem solution
    {Ω : Type*}
    (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hStart : 0 ≤ X 0 ω) :
    firstNegativePassage X ω =
      firstNonpositiveLattice
        (fun t η => X t η + 1) ω := by
  classical
  have hh : ∀ t : ℝ≥0,
      (0 < t ∧ X t ω < 0) ↔ X t ω + 1 ≤ 0 := by
    intro t
    constructor
    · rintro ⟨_, hx⟩
      omega
    · intro hx
      have hneg : X t ω < 0 := by omega
      constructor
      · by_contra hnot
        have ht0 : t = 0 := le_antisymm (le_of_not_gt hnot) (zero_le : (0 : ℝ≥0) ≤ t)
        subst t
        omega
      · exact hneg
  have hsets :
      ({t : ℝ≥0 | 0 < t ∧ X t ω < 0} : Set ℝ≥0) =
      {t : ℝ≥0 | X t ω + 1 ≤ 0} := by
    ext t
    exact hh t
  have he :
      (∃ t : ℝ≥0, 0 < t ∧ X t ω < 0) ↔
      (∃ t : ℝ≥0, X t ω + 1 ≤ 0) := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, (hh t).mp ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, (hh t).mpr ht⟩
  unfold firstNegativePassage firstNonpositiveLattice
  by_cases h : ∃ t : ℝ≥0, 0 < t ∧ X t ω < 0
  · rw [if_pos h, if_pos (he.mp h), hsets]
  · rw [if_neg h, if_neg (fun hz => h (he.mpr hz))]
