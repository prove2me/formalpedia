-- Prove2me | solution 1 for KernelRamsey.nonnbr_false
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:45:10.293206+00:00
-- url     : https://prove2.me/submissions/d7456469-0997-4c70-8ade-8db945b313d2

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem solution {V : Type} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] {t m : Nat} (h : Ram (t - 1) m) (ht : 1 ≤ t) {A : Finset V}
    (hnoT : ∀ T ⊆ A, ¬ G.IsNClique 3 T) (hnoI : ∀ I ⊆ A, ¬ Gᶜ.IsNClique t I)
    {v : V} (hv : v ∈ A) (hM : m ≤ (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card) : False := by
  rcases h G _ hM with ⟨T, hTM, hT⟩ | ⟨I, hIM, hI⟩
  · exact hnoT T (fun x hx => (Finset.mem_filter.mp (hTM hx)).1) hT
  · apply hnoI (insert v I)
    · intro x hx
      simp only [mem_insert] at hx
      rcases hx with rfl | hx
      · exact hv
      · exact (Finset.mem_filter.mp (hIM hx)).1
    · have hvI : v ∉ I := fun hh => (Finset.mem_filter.mp (hIM hh)).2.1 rfl
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        simp only [coe_insert, Set.mem_insert_iff] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact ⟨hxy, (Finset.mem_filter.mp (hIM hy)).2.2⟩
        · exact ⟨hxy, fun hadj => (Finset.mem_filter.mp (hIM hx)).2.2 hadj.symm⟩
        · exact hI.1 hx hy hxy
      · rw [Finset.card_insert_of_notMem hvI, hI.2]
        omega
