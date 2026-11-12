-- Prove2me | solution 1 for GroupLabeledMatroid.Proximity.circuit_base_exchange
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:46:39.852932+00:00
-- url     : https://prove2.me/submissions/69f2c361-6b2e-4c2d-b05f-8a017dc4030a

import Mathlib

set_option autoImplicit false

/-- Circuit/base exchange: an edge of a circuit outside a base can replace a common element. -/
theorem solution {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matroid E) (B C : Finset E) (hB : M.IsBase (B : Set E))
    (hC : M.IsCircuit (C : Set E)) (b : E) (hb : b ∈ B ∩ C) :
    ∃ a ∈ C \ B, M.IsBase ((insert a (B.erase b) : Finset E) : Set E) := by
  classical
  have hbB : b ∈ (B : Set E) := by
    have := Finset.mem_inter.mp hb
    exact this.1
  have hbC : b ∈ (C : Set E) := by
    have := Finset.mem_inter.mp hb
    exact this.2
  let K : Set E := M.fundCocircuit b (B : Set E)
  have hK : M.IsCocircuit K := Matroid.fundCocircuit_isCocircuit (e := b) hbB hB
  have hbK : b ∈ K := Matroid.mem_fundCocircuit M b (B : Set E)
  have hne : ((C : Set E) ∩ K) ≠ {b} := hC.inter_isCocircuit_ne_singleton (e := b) hK
  have hex : ∃ a, a ∈ C ∧ a ∈ K ∧ a ≠ b := by
    by_contra h
    push Not at h
    exact hne (by
      ext x
      constructor
      · intro hx
        exact Set.mem_singleton_iff.mpr (h x hx.1 hx.2)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ⟨hbC, hbK⟩)
  obtain ⟨a, haC, haK, hab⟩ := hex
  have haB : a ∉ (B : Set E) := by
    intro ha
    have hinter : a ∈ (M.fundCocircuit b (B : Set E)) ∩ (B : Set E) := ⟨haK, ha⟩
    rw [M.fundCocircuit_inter_eq hbB] at hinter
    exact hab (Set.mem_singleton_iff.mp hinter)
  have hbF : b ∈ M.fundCircuit a (B : Set E) :=
    (hB.mem_fundCocircuit_iff_mem_fundCircuit (e := a) (f := b)).mp haK
  have hcl : a ∈ M.closure (B : Set E) := by
    rw [hB.closure_eq]
    rcases M.fundCocircuit_subset_insert_compl b (B : Set E) haK with h | h
    · rw [h]
      exact hB.subset_ground hbB
    · exact h.1
  have hIndep : M.Indep (insert a (B : Set E) \ {b}) :=
    (hB.indep.mem_fundCircuit_iff (e := a) (x := b) hcl haB).mp hbF
  have hIndep' : M.Indep (insert a ((B : Set E) \ {b})) := by
    rw [Set.insert_sdiff_singleton_comm hab]
    exact hIndep
  have hbase : M.IsBase (insert a ((B : Set E) \ {b})) :=
    hB.exchange_isBase_of_indep (e := b) (f := a) haB hIndep'
  refine ⟨a, ?_, ?_⟩
  · rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_coe.mp haC, fun ha => haB (Finset.mem_coe.mpr ha)⟩
  · simpa using hbase
