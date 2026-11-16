-- Prove2me | solution 1 for Kyprianou.Ch06.iIndepFunOfFullRectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:09:56.884433+00:00
-- url     : https://prove2.me/submissions/bd3f2392-76e3-4460-959a-8a8f77143d22

import Mathlib.Probability.Independence.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Independent coordinate rectangles over all finite-dimensional coordinates
imply the standard independent-random-functions predicate. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (n : Nat) (f : Fin n → Ω → Real)
    (hrect : ∀ A : Fin n → Set Real,
      (∀ i, MeasurableSet (A i)) →
      P {ω | ∀ i : Fin n, f i ω ∈ A i} =
        ∏ i : Fin n, P {ω | f i ω ∈ A i}) :
    ProbabilityTheory.iIndepFun f P := by
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let A : Fin n → Set Real := fun i =>
    if i ∈ S then sets i else Set.univ
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa [A, hi] using hsets i hi
    · simp [A, hi]
  have hset :
      (⋂ i ∈ S, f i ⁻¹' sets i) = {ω | ∀ i : Fin n, f i ω ∈ A i} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro hh i
      by_cases hi : i ∈ S
      · simpa [A, hi] using hh i hi
      · simp [A, hi]
    · intro hh i hi
      simpa [A, hi] using hh i
  rw [hset, hrect A hA]
  have hcoordinate : ∀ i : Fin n,
      P {ω | f i ω ∈ A i} =
        if i ∈ S then P (f i ⁻¹' sets i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [A, if_pos hi]
      rfl
    · simpa [A, hi] using hprob
  simp_rw [hcoordinate]
  simp [Finset.prod_ite]
