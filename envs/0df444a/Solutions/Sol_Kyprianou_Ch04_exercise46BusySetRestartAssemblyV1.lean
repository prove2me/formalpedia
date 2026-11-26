-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusySetRestartAssemblyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:34:03.294191+00:00
-- url     : https://prove2.me/submissions/33a42cad-8945-409b-9841-34bc644fbd94

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (S T : Set NNReal) (a b : NNReal)
    (ha : a ∈ S) (hab : a ≤ b)
    (hBefore : ∀ t ∈ S, t ≤ b → t = a)
    (hPos : ∀ u ∈ T, 0 < u)
    (hShift : ∀ u : NNReal, 0 < u → (b+u ∈ S ↔ u ∈ T)) :
    S = insert a ((fun u : NNReal => b+u) '' T) := by
  ext t
  constructor
  · intro ht
    by_cases h : t ≤ b
    · exact mem_insert_iff.mpr (Or.inl (hBefore t ht h))
    · have hbt : b < t := lt_of_not_ge h
      have he : b + (t-b) = t := add_tsub_cancel_of_le hbt.le
      have hp : 0 < t-b := tsub_pos_of_lt hbt
      exact mem_insert_of_mem _ ⟨t-b, (hShift _ hp).mp (he.symm ▸ ht), he⟩
  · rintro (rfl | ⟨u, hu, rfl⟩)
    · exact ha
    · exact (hShift _ (hPos u hu)).mpr hu
