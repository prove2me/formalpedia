-- Prove2me | solution 1 for IntermediateField.finiteDimensional_adjoin_and_finrank_le_of_forall_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/94f7abea-5bfe-5f22-98fd-c0fd82760e33

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset

set_option autoImplicit false

open IntermediateField in
theorem solution
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E) (n : ℕ)
    (hS : ∀ s : Finset E, (↑s : Set E) ⊆ S →
      FiniteDimensional F ↥(IntermediateField.adjoin F (↑s : Set E)) ∧
        Module.finrank F ↥(IntermediateField.adjoin F (↑s : Set E)) ≤ n) :
    FiniteDimensional F ↥(IntermediateField.adjoin F S) ∧ Module.finrank F ↥(IntermediateField.adjoin F S) ≤ n := by
  classical

  let D : Set ℕ := {d | ∃ s : Finset E, (↑s : Set E) ⊆ S ∧ Module.finrank F ↥(adjoin F (↑s : Set E)) = d}
  have hDne : D.Nonempty := ⟨_, ∅, by simp, rfl⟩
  have hDbdd : BddAbove D := ⟨n, by rintro d ⟨s, hs, rfl⟩; exact (hS s hs).2⟩
  obtain ⟨s₀, hs₀, hmax⟩ : ∃ s₀ : Finset E, (↑s₀ : Set E) ⊆ S ∧
      ∀ s : Finset E, (↑s : Set E) ⊆ S → Module.finrank F ↥(adjoin F (↑s : Set E)) ≤ Module.finrank F ↥(adjoin F (↑s₀ : Set E)) := by
    obtain ⟨s₀, hs₀, hd⟩ := Nat.sSup_mem hDne hDbdd
    exact ⟨s₀, hs₀, fun s hs => hd ▸ le_csSup hDbdd ⟨s, hs, rfl⟩⟩
  haveI hfin₀ : FiniteDimensional F ↥(adjoin F (↑s₀ : Set E)) := (hS s₀ hs₀).1

  have hsub : S ⊆ (adjoin F (↑s₀ : Set E) : Set E) := by
    intro x hx
    let s₁ : Finset E := insert x s₀
    have hs₁ : (↑s₁ : Set E) ⊆ S := by
      intro y hy
      rw [Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact hs₀ hy
    haveI hfin₁ : FiniteDimensional F ↥(adjoin F (↑s₁ : Set E)) := (hS s₁ hs₁).1
    have hle : adjoin F (↑s₀ : Set E) ≤ adjoin F (↑s₁ : Set E) :=
      adjoin.mono F _ _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hdim : Module.finrank F ↥(adjoin F (↑s₁ : Set E)) ≤ Module.finrank F ↥(adjoin F (↑s₀ : Set E)) := hmax s₁ hs₁
    have heq : adjoin F (↑s₀ : Set E) = adjoin F (↑s₁ : Set E) :=
      IntermediateField.eq_of_le_of_finrank_le hle hdim
    have hx₁ : x ∈ adjoin F (↑s₁ : Set E) := subset_adjoin F _ (by rw [Finset.coe_insert]; exact Set.mem_insert _ _)
    rw [← heq] at hx₁
    exact hx₁
  have hSeq : adjoin F S = adjoin F (↑s₀ : Set E) :=
    le_antisymm (adjoin_le_iff.mpr hsub) (adjoin.mono F _ _ hs₀)
  rw [hSeq]
  exact ⟨hfin₀, (hS s₀ hs₀).2⟩

end S_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset
end P2MW
export P2MW.S_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset (solution)
