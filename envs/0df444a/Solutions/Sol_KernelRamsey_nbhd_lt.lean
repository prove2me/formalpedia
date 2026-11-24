-- Prove2me | solution 1 for KernelRamsey.nbhd_lt
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:29:02.54623+00:00
-- url     : https://prove2.me/submissions/8b28eb4d-4890-40f2-9532-01b7bb90d792

import Mathlib
open Finset

theorem solution {V : Type} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] {t : Nat} {A : Finset V}
    (hnoT : ∀ T ⊆ A, ¬ G.IsNClique 3 T) (hnoI : ∀ I ⊆ A, ¬ Gᶜ.IsNClique t I)
    {v : V} (hv : v ∈ A) : (A.filter (fun w => G.Adj v w)).card < t := by
  by_contra hge
  push Not at hge
  obtain ⟨I, hIN, hI⟩ := Finset.exists_subset_card_eq hge
  apply hnoI I (fun x hx => (Finset.mem_filter.mp (hIN hx)).1)
  refine ⟨?_, hI⟩
  intro a ha b hb hab
  refine ⟨hab, fun hadj => ?_⟩
  have haN := Finset.mem_filter.mp (hIN ha)
  have hbN := Finset.mem_filter.mp (hIN hb)
  apply hnoT {v, a, b} (by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hv
    · exact haN.1
    · exact hbN.1)
  refine ⟨?_, ?_⟩
  · have h1 : G.Adj v a := haN.2
    have h2 : G.Adj v b := hbN.2
    have h1' := h1.symm
    have h2' := h2.symm
    have h3 := hadj
    have h3' := hadj.symm
    intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> subst hx <;> subst hy <;>
      first
      | exact absurd rfl hxy
      | assumption
  · have hva : v ≠ a := fun e => by have := haN.2; rw [← e] at this; exact G.loopless.irrefl _ this
    have hvb : v ≠ b := fun e => by have := hbN.2; rw [← e] at this; exact G.loopless.irrefl _ this
    rw [Finset.card_insert_of_notMem (by simp [hva, hvb]), Finset.card_pair hab]
