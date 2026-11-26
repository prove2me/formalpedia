-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PredictableTimeCapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:47.678667+00:00
-- url     : https://prove2.me/submissions/d38a2476-310b-4421-85d2-ff35645749b5

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (T : NNReal) :
    MeasurableSet[G.predictable] {p : NNReal × Omega | p.1 ≤ T} := by
  have he : {p : NNReal × Omega | p.1 ≤ T} =
      ({0} : Set NNReal) ×ˢ (univ : Set Omega) ∪ Ioc 0 T ×ˢ (univ : Set Omega) := by
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_prod, mem_singleton_iff, mem_univ,
      and_true, mem_Ioc]
    constructor
    · intro h
      rcases eq_or_lt_of_le (show 0 ≤ p.1 from zero_le) with he | hp
      · exact Or.inl he.symm
      · exact Or.inr ⟨hp,h⟩
    · rintro (h | h)
      · rw [h]; exact zero_le
      · exact h.2
  rw [he]
  exact (measurableSet_predictable_singleton_bot_prod MeasurableSet.univ).union
    (measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ)
