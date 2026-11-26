-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49FiniteRepresentativeSublevelV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:38.731244+00:00
-- url     : https://prove2.me/submissions/cd6de52b-9ccc-44b5-996d-2e91a79064c5

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false


theorem solution {Ω : Type} [MeasurableSpace Ω]
    (τ : Ω → WithTop NNReal) (E : Set Ω) (hE : MeasurableSet E)
    (hfin : ∀ ω ∈ E, τ ω ≠ ⊤)
    (f : Ω → NNReal) (hf : Measurable f)
    (heq : ∀ ω, τ ω ≠ ⊤ → τ ω = (f ω : WithTop NNReal))
    (a : NNReal) :
    MeasurableSet (E ∩ {ω | τ ω ≤ (a : WithTop NNReal)}) := by
  have hs : E ∩ {ω | τ ω ≤ (a : WithTop NNReal)} = E ∩ f ⁻¹' Iic a := by
    ext ω
    by_cases hω : ω ∈ E
    · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_Iic, hω, true_and, heq ω (hfin ω hω)]
      exact WithTop.coe_le_coe
    · simp [hω]
  rw [hs]
  exact hE.inter (hf measurableSet_Iic)
