-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_full_fiber_eq_indicator_ae
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:18:01.915845+00:00
-- url     : https://prove2.me/submissions/eced4bb2-82bf-4ca4-b30d-4a24c04341d5

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem solution
    (n : Nat) (T : Real) (hT : 0 < T) :
    (fun t : Real => Set.indicator (Set.Ioo (0 : Real) T)
      (fun u => MeasureTheory.volume
        {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - u}) t) =ᵐ[MeasureTheory.volume]
    (fun t : Real => MeasureTheory.volume
      {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}) := by
  filter_upwards [MeasureTheory.volume.ae_ne (0 : Real)] with t ht0
  by_cases ht : 0 < t
  · by_cases htT : t < T
    · have hsets :
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} =
          {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} := by
        ext y
        simp [ht.le]
      have hmem : t ∈ Set.Ioo (0 : Real) T := ⟨ht, htT⟩
      simp [Set.indicator, hmem, hsets]
    · have hTt : T ≤ t := le_of_not_gt htT
      have hempty :
          {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} = ∅ := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, hy, hsumlt⟩
        have hsum : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg fun i _ => hy i
        have hbound : T - t ≤ 0 := sub_nonpos.mpr hTt
        linarith
      have hnotmem : t ∉ Set.Ioo (0 : Real) T := by
        intro h
        exact (not_lt_of_ge hTt) h.2
      simp [Set.indicator, hnotmem, hempty]
  · have htnle : t ≤ 0 := le_of_not_gt ht
    have htneg : t < 0 := lt_of_le_of_ne htnle ht0
    have hmem : t ∉ Set.Ioo (0 : Real) T := by
      intro h
      exact (not_lt_of_ge htnle) h.1
    have hleft : Set.indicator (Set.Ioo (0 : Real) T)
        (fun u => MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - u}) t = 0 := by
      simp [Set.indicator, hmem]
    have hempty :
        {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨htle, _, _⟩
      exact (not_le_of_gt htneg) htle
    have hright : MeasureTheory.volume
        {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} = 0 := by
      rw [hempty]
      simp
    rw [hleft, hright]
