-- Prove2me | solution 1 for KernelRamsey.ram_two_three
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:45:07.494803+00:00
-- url     : https://prove2.me/submissions/87a4c68d-9595-49da-9180-e433f5daecf9

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem solution : Ram 2 3 := by
  classical
  intro V G A hA
  by_cases h : ∃ I ⊆ A, Gᶜ.IsNClique 2 I
  · exact Or.inr h
  · left
    push Not at h
    obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq hA
    refine ⟨T, hTA, ?_, hT⟩
    intro a ha b hb hab
    by_contra hnadj
    apply h {a, b} (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact hTA ‹_›)
    refine ⟨?_, by simp [hab]⟩
    intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact ⟨hab, hnadj⟩
    · exact ⟨hab.symm, fun h' => hnadj h'.symm⟩
    · exact absurd rfl hxy
