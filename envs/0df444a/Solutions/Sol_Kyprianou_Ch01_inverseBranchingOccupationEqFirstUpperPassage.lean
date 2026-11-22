-- Prove2me | solution 1 for Kyprianou.Ch01.inverseBranchingOccupationEqFirstUpperPassage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:28:50.802832+00:00
-- url     : https://prove2.me/submissions/d6247c4e-cdc0-413d-a2f0-b3d95e18ce16

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict first upper passage of the occupation primitive coincides with
the original inverse Lamperti occupation clock, including the top case. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    inverseBranchingOccupation Y t ω =
      firstUpperPassage
        (fun s (η : Ω) => branchingOccupation Y s η)
        (t : ℝ) ω := by
  classical
  have hzero : branchingOccupation Y 0 ω = 0 := by
    simp [branchingOccupation]
  have hpos : ∀ s : ℝ≥0,
      (t : ℝ) < branchingOccupation Y s ω → 0 < s := by
    intro s hs
    by_contra h
    have hs0 : s = 0 := le_antisymm (le_of_not_gt h) (zero_le : (0 : ℝ≥0) ≤ s)
    subst s
    rw [hzero] at hs
    exact (not_lt_of_ge (NNReal.coe_nonneg t)) hs
  have hsets : ({s : ℝ≥0 | (t : ℝ) < branchingOccupation Y s ω} : Set ℝ≥0) =
      {s : ℝ≥0 | 0 < s ∧ (t : ℝ) < branchingOccupation Y s ω} := by
    ext s
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => ⟨hpos s h, h⟩, fun h => h.2⟩
  have hexists :
      (∃ s : ℝ≥0, (t : ℝ) < branchingOccupation Y s ω) ↔
      (∃ s : ℝ≥0, 0 < s ∧ (t : ℝ) < branchingOccupation Y s ω) := by
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, hpos s hs, hs⟩
    · rintro ⟨s, _, hs⟩
      exact ⟨s, hs⟩
  change
    (if ∃ s : ℝ≥0, (t : ℝ) < branchingOccupation Y s ω then
      ((sInf {s : ℝ≥0 | (t : ℝ) < branchingOccupation Y s ω} : ℝ≥0) :
        WithTop ℝ≥0) else ⊤) =
    (if ∃ s : ℝ≥0, 0 < s ∧ (t : ℝ) < branchingOccupation Y s ω then
      ((sInf {s : ℝ≥0 |
        0 < s ∧ (t : ℝ) < branchingOccupation Y s ω} : ℝ≥0) :
        WithTop ℝ≥0) else ⊤)
  by_cases he : ∃ s : ℝ≥0, (t : ℝ) < branchingOccupation Y s ω
  · rw [if_pos he, if_pos (hexists.mp he), hsets]
  · rw [if_neg he, if_neg (fun h => he (hexists.mpr h))]
