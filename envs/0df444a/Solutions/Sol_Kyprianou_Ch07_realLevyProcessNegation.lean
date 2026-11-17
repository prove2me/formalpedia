-- Prove2me | solution 1 for Kyprianou.Ch07.realLevyProcessNegation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:40:16.473274+00:00
-- url     : https://prove2.me/submissions/47bd9b23-8f3b-4f4e-a119-f728d3090ffe

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X) :
    Kyprianou.Ch06.IsRealLevyProcess P
      (fun t omega => -X t omega) := by
  rcases hX with ⟨hmeas, hzero, hstation, hindep, hreg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (hmeas t).neg
  · filter_upwards [hzero] with omega h
    simp [h]
  · intro s t
    have h := congrArg
      (fun mu : Measure Real => mu.map (fun x : Real => -x))
      (hstation s t)
    have hs : Measurable (fun omega => X (s + t) omega - X s omega) :=
      (hmeas (s + t)).sub (hmeas s)
    have ht : Measurable (X t) := hmeas t
    rw [Measure.map_map measurable_neg hs,
      Measure.map_map measurable_neg ht] at h
    convert h using 1
    · congr 1
      funext omega
      simp only [Function.comp_def]
      ring
    · rfl
  · intro n times ht A hA
    let B : Fin n → Set Real := fun i => {x : Real | -x ∈ A i}
    have hB : ∀ i : Fin n, MeasurableSet (B i) := by
      intro i
      exact (hA i).preimage measurable_neg
    have h := hindep n times ht B hB
    simpa only [B, Set.mem_setOf_eq, neg_sub,
      sub_neg_eq_add, add_comm, sub_eq_add_neg, neg_add] using h
  · filter_upwards [hreg] with omega h
    intro t
    rcases h t with ⟨hc, hl⟩
    constructor
    · exact hc.neg
    · rcases hl with ht | ⟨x, hx⟩
      · exact Or.inl ht
      · exact Or.inr ⟨-x, hx.neg⟩
