-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46LeftIsolatedCountableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:35:30.523697+00:00
-- url     : https://prove2.me/submissions/19f358d9-453c-4f62-89c6-e0a0f636b152

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (S : Set NNReal)
    (h : ∀ t ∈ S, ∃ a : NNReal, a < t ∧
      ∀ u ∈ S, a < u → u < t → False) :
    S.Countable := by
  apply (countable_setOfPred_isolated_left_within (s := S)).mono
  intro t ht
  refine ⟨ht, ?_⟩
  obtain ⟨a, ha, hgap⟩ := h t ht
  rw [← empty_mem_iff_bot]
  have he : Ioi a ∈ nhdsWithin t (S ∩ Iio t) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha)
  filter_upwards [he, self_mem_nhdsWithin] with u hu hU
  exact (hgap u hU.1 hu hU.2).elim
