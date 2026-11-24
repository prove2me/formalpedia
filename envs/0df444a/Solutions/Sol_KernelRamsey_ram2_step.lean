-- Prove2me | solution 1 for KernelRamsey.ram2_step
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:47:00.476206+00:00
-- url     : https://prove2.me/submissions/4aaddc95-e79f-43c1-b50f-54cfe2a592ab

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_card_split
open KernelRamsey Finset

theorem solution {s t a b : Nat} (hs : 2 ≤ s) (ht : 2 ≤ t) (hab : 1 ≤ a + b)
    (ha : Ram2 (s - 1) t a) (hb : Ram2 s (t - 1) b) : Ram2 s t (a + b) := by
  classical
  intro V G A hA
  by_contra hno
  push Not at hno
  obtain ⟨hnoT, hnoI⟩ := hno
  have hpos : 0 < A.card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  have hs' := card_split G A hv
  by_cases hNa : a ≤ (A.filter (fun w => G.Adj v w)).card
  · rcases ha G _ hNa with ⟨T, hTN, hT⟩ | ⟨I, hIN, hI⟩
    · apply hnoT (insert v T)
      · intro x hx
        simp only [mem_insert] at hx
        rcases hx with rfl | hx
        · exact hv
        · exact (Finset.mem_filter.mp (hTN hx)).1
      · have hvT : v ∉ T := fun hh => G.loopless.irrefl _ (Finset.mem_filter.mp (hTN hh)).2
        refine ⟨?_, ?_⟩
        · intro x hx y hy hxy
          simp only [coe_insert, Set.mem_insert_iff] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact absurd rfl hxy
          · exact (Finset.mem_filter.mp (hTN hy)).2
          · exact (Finset.mem_filter.mp (hTN hx)).2.symm
          · exact hT.1 hx hy hxy
        · rw [Finset.card_insert_of_notMem hvT, hT.2]
          omega
    · exact hnoI I (fun x hx => (Finset.mem_filter.mp (hIN hx)).1) hI
  · push Not at hNa
    have hMb : b ≤ (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by omega
    rcases hb G _ hMb with ⟨T, hTM, hT⟩ | ⟨I, hIM, hI⟩
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
