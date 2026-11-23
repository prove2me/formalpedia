-- Prove2me | solution 1 for Kyprianou.Ch01.inverseReciprocalOccupationBoundaryFromClockBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:59:51.38858+00:00
-- url     : https://prove2.me/submissions/234ff95d-2363-4049-8e58-cf0648ff517f

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (t a b : ℝ≥0) (hab : a < b)
    (hBefore : ∀ u : ℝ≥0, u < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞))
    (hAfter : ∀ u : ℝ≥0, a < u → u < b →
      reciprocalOccupation X u ω = ⊤) :
    inverseReciprocalOccupation X t ω = (a : WithTop ℝ≥0) := by
  let S : Set ℝ≥0 := {u | (t : ℝ≥0∞) < reciprocalOccupation X u ω}
  have hSN : S.Nonempty := by
    obtain ⟨v, hav, hvb⟩ := exists_between hab
    refine ⟨v, ?_⟩
    change (t : ℝ≥0∞) < reciprocalOccupation X v ω
    rw [hAfter v hav hvb]
    exact ENNReal.coe_lt_top
  have hSbdd : BddBelow S := ⟨0, by intro v hv; exact bot_le⟩
  have hInfLower : a ≤ sInf S := by
    apply le_csInf hSN
    intro u hu
    by_contra hnot
    have hua : u < a := lt_of_not_ge hnot
    exact (not_lt_of_ge (hBefore u hua)) hu
  have hInfUpper : sInf S ≤ a := by
    by_contra hnot
    have haInf : a < sInf S := lt_of_not_ge hnot
    obtain ⟨v, hav, hvmin⟩ := exists_between (lt_min hab haInf)
    have hvb : v < b := lt_of_lt_of_le hvmin (min_le_left _ _)
    have hvInf : v < sInf S :=
      lt_of_lt_of_le hvmin (min_le_right _ _)
    have hvS : v ∈ S := by
      change (t : ℝ≥0∞) < reciprocalOccupation X v ω
      rw [hAfter v hav hvb]
      exact ENNReal.coe_lt_top
    have hInfV : sInf S ≤ v := csInf_le hSbdd hvS
    exact (not_le_of_gt hvInf) hInfV
  have hInf : sInf S = a := le_antisymm hInfUpper hInfLower
  have hExists : ∃ v : ℝ≥0,
      (t : ℝ≥0∞) < reciprocalOccupation X v ω := hSN
  unfold inverseReciprocalOccupation
  simp only [if_pos hExists]
  exact congrArg (fun u : ℝ≥0 => (u : WithTop ℝ≥0)) hInf
