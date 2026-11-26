-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41GridFirstSublevelV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:33:03.977901+00:00
-- url     : https://prove2.me/submissions/3fce982a-853b-4706-bd47-d00748761d83

import Mathlib
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

open Kyprianou.Ch04

open Kyprianou.Ch04

theorem solution {Ω : Type}
    (D : Finset NNReal) (C : NNReal → Set Ω)
    (b s : NNReal) (ω : Ω) :
    ((∃ t ∈ D, ω ∈ C t) ∧ exercise41GridFirstV2 D C b ω ≤ s) ↔
      ∃ t ∈ D, ω ∈ C t ∧ t ≤ s := by
  classical
  let H := D.filter (fun t => ω ∈ C t)
  by_cases h : H.Nonempty
  · have hm : H.min' h ∈ H := Finset.min'_mem H h
    have hm' := Finset.mem_filter.mp hm
    change ((∃ t ∈ D, ω ∈ C t) ∧
      (if k : H.Nonempty then H.min' k else b) ≤ s) ↔ _
    rw [dif_pos h]
    constructor
    · intro hs
      exact ⟨H.min' h, hm'.1, hm'.2, hs.2⟩
    · rintro ⟨t, ht, hc, hts⟩
      exact ⟨⟨t, ht, hc⟩, (Finset.min'_le H t
        (Finset.mem_filter.mpr ⟨ht, hc⟩)).trans hts⟩
  · constructor
    · rintro ⟨⟨t, ht, hc⟩, _⟩
      exact (h ⟨t, Finset.mem_filter.mpr ⟨ht, hc⟩⟩).elim
    · rintro ⟨t, ht, hc, _⟩
      exact (h ⟨t, Finset.mem_filter.mpr ⟨ht, hc⟩⟩).elim
