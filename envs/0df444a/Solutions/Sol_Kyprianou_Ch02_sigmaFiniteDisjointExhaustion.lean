-- Prove2me | solution 1 for Kyprianou.Ch02.sigmaFiniteDisjointExhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:36:13.345624+00:00
-- url     : https://prove2.me/submissions/9d214926-26fc-4ea1-bbfd-44cbca881951

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false


universe u

theorem solution
    (E : Type u) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] :
    ∃ s : ℕ → Set E,
      (∀ n, MeasurableSet (s n)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) ∧
      (∀ n, ν (s n) < ⊤) ∧
      (⋃ n, s n) = Set.univ := by
  refine ⟨disjointed (MeasureTheory.spanningSets ν), ?_, ?_, ?_, ?_⟩
  · intro n
    exact MeasurableSet.disjointed (MeasureTheory.measurableSet_spanningSets ν) n
  · exact disjoint_disjointed _
  · intro n
    refine lt_of_le_of_lt ?_ (MeasureTheory.measure_spanningSets_lt_top ν n)
    exact MeasureTheory.measure_mono (disjointed_subset _ _)
  · rw [iUnion_disjointed]
    exact MeasureTheory.iUnion_spanningSets ν

