-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41GridFirstStoppingV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:36:47.131949+00:00
-- url     : https://prove2.me/submissions/87e5c053-e666-43e5-883a-f8a226a806e6

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstSublevelV2
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

open Kyprianou.Ch04

open Kyprianou.Ch04

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (D : Finset NNReal) (C : NNReal → Set Ω) (b : NNReal)
    (hDb : ∀ t ∈ D, t ≤ b)
    (hC : ∀ t, MeasurableSet[F t] (C t)) :
    let τ := exercise41GridFirstV2 D C b
    let A : Set Ω := {ω | ∃ t ∈ D, ω ∈ C t}
    (∀ s, MeasurableSet[F s] {ω | τ ω ≤ s}) ∧
    (∀ s, MeasurableSet[F s] (A ∩ {ω | τ ω ≤ s})) := by
  classical
  dsimp only
  let τ := exercise41GridFirstV2 D C b
  let A : Set Ω := {ω | ∃ t ∈ D, ω ∈ C t}
  have hcap (ω : Ω) : τ ω ≤ b := by
    let H := D.filter (fun t => ω ∈ C t)
    change (if h : H.Nonempty then H.min' h else b) ≤ b
    split
    · rename_i h
      exact hDb _ (Finset.mem_filter.mp (Finset.min'_mem H h)).1
    · exact le_rfl
  have hPast (s : NNReal) :
      MeasurableSet[F s] (A ∩ {ω | τ ω ≤ s}) := by
    have heq : A ∩ {ω | τ ω ≤ s} =
        ⋃ t : ↥(D.filter (fun t => t ≤ s)), C (t : NNReal) := by
      ext ω
      change ((∃ t ∈ D, ω ∈ C t) ∧ τ ω ≤ s) ↔ _
      rw [exercise41GridFirstSublevelV2, Set.mem_iUnion]
      constructor
      · rintro ⟨t, ht, hc, hts⟩
        exact ⟨⟨t, Finset.mem_filter.mpr ⟨ht, hts⟩⟩, hc⟩
      · rintro ⟨t, hc⟩
        exact ⟨t, (Finset.mem_filter.mp t.property).1,
          hc, (Finset.mem_filter.mp t.property).2⟩
    rw [heq]
    exact MeasurableSet.iUnion fun t =>
      F.mono (Finset.mem_filter.mp t.property).2 _ (hC t)
  refine ⟨?_, hPast⟩
  intro s
  by_cases hs : b ≤ s
  · have heq : {ω | τ ω ≤ s} = Set.univ :=
      Set.eq_univ_of_forall fun ω => (hcap ω).trans hs
    rw [heq]
    exact MeasurableSet.univ
  · have heq : {ω | τ ω ≤ s} = A ∩ {ω | τ ω ≤ s} := by
      ext ω
      change τ ω ≤ s ↔ (∃ t ∈ D, ω ∈ C t) ∧ τ ω ≤ s
      constructor
      · intro hle
        refine ⟨?_, hle⟩
        by_contra hn
        let H := D.filter (fun t => ω ∈ C t)
        have hEmpty : ¬ H.Nonempty := by
          rintro ⟨t, ht⟩
          exact hn ⟨t, (Finset.mem_filter.mp ht).1,
            (Finset.mem_filter.mp ht).2⟩
        change (if h : H.Nonempty then H.min' h else b) ≤ s at hle
        rw [dif_neg hEmpty] at hle
        exact hs hle
      · exact And.right
    rw [heq]
    exact hPast s
