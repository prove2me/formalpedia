-- Prove2me | solution 1 for HyperKCut.Structure.cut_sym_submod
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:10:41.948832+00:00
-- url     : https://prove2.me/submissions/088b5365-0b61-4d66-926c-780e57d26a4a

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun

open HyperKCut.Structure

theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V) :
    NonmonotoneSubmod.Shared.SymmetricSetFun (fun A => (d H A : ℝ)) ∧
    NonmonotoneSubmod.Shared.Submodular (fun A => (d H A : ℝ)) := by
  classical
  have key : ∀ (E : Multiset (Finset V)) (p q r s : Finset V → Prop)
      [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s],
      (∀ e, (if p e then 1 else 0) + (if q e then 1 else 0) ≤
        (if r e then 1 else 0) + (if s e then (1 : ℕ) else 0)) →
      (E.filter p).card + (E.filter q).card ≤ (E.filter r).card + (E.filter s).card := by
    intro E p q r s _ _ _ _ h
    induction E using Multiset.induction_on with
    | empty => simp
    | cons a E ih =>
      have ha := h a
      simp only [Multiset.filter_cons]
      split_ifs at ha ⊢ <;> simp <;> omega
  refine ⟨?_, ?_⟩
  · intro A
    have h : d H Aᶜ = d H A := by
      unfold d
      congr 1
      apply Multiset.filter_congr
      intro e _
      simp only [compl_compl]
      exact and_comm
    simp only [h]
  · intro A B
    simp only
    have : d H (A ∪ B) + d H (A ∩ B) ≤ d H A + d H B := by
      unfold d
      apply key
      intro e
      simp only [Meets, Finset.Nonempty, Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
      by_cases h1 : (∃ x, x ∈ e ∧ (x ∈ A ∨ x ∈ B)) ∧ ∃ x, x ∈ e ∧ ¬(x ∈ A ∨ x ∈ B)
      · by_cases h2 : (∃ x, x ∈ e ∧ (x ∈ A ∧ x ∈ B)) ∧ ∃ x, x ∈ e ∧ ¬(x ∈ A ∧ x ∈ B)
        · have hA : (∃ x, x ∈ e ∧ x ∈ A) ∧ ∃ x, x ∈ e ∧ x ∉ A := by
            obtain ⟨⟨x, hx, hxA, -⟩, -⟩ := h2
            obtain ⟨-, ⟨y, hy, hyn⟩⟩ := h1
            exact ⟨⟨x, hx, hxA⟩, ⟨y, hy, fun h => hyn (Or.inl h)⟩⟩
          have hB : (∃ x, x ∈ e ∧ x ∈ B) ∧ ∃ x, x ∈ e ∧ x ∉ B := by
            obtain ⟨⟨x, hx, -, hxB⟩, -⟩ := h2
            obtain ⟨-, ⟨y, hy, hyn⟩⟩ := h1
            exact ⟨⟨x, hx, hxB⟩, ⟨y, hy, fun h => hyn (Or.inr h)⟩⟩
          rw [if_pos h1, if_pos h2, if_pos hA, if_pos hB]
        · have : ((∃ x, x ∈ e ∧ x ∈ A) ∧ ∃ x, x ∈ e ∧ x ∉ A) ∨
              ((∃ x, x ∈ e ∧ x ∈ B) ∧ ∃ x, x ∈ e ∧ x ∉ B) := by
            obtain ⟨⟨x, hx, hxAB⟩, ⟨y, hy, hyn⟩⟩ := h1
            rcases hxAB with hxA | hxB
            · exact Or.inl ⟨⟨x, hx, hxA⟩, ⟨y, hy, fun h => hyn (Or.inl h)⟩⟩
            · exact Or.inr ⟨⟨x, hx, hxB⟩, ⟨y, hy, fun h => hyn (Or.inr h)⟩⟩
          rw [if_pos h1, if_neg h2]
          rcases this with h | h
          · rw [if_pos h]; split_ifs <;> omega
          · rw [if_pos h]; split_ifs <;> omega
      · by_cases h2 : (∃ x, x ∈ e ∧ (x ∈ A ∧ x ∈ B)) ∧ ∃ x, x ∈ e ∧ ¬(x ∈ A ∧ x ∈ B)
        · have : ((∃ x, x ∈ e ∧ x ∈ A) ∧ ∃ x, x ∈ e ∧ x ∉ A) ∨
              ((∃ x, x ∈ e ∧ x ∈ B) ∧ ∃ x, x ∈ e ∧ x ∉ B) := by
            obtain ⟨⟨x, hx, hxA, hxB⟩, ⟨y, hy, hyn⟩⟩ := h2
            by_cases hyA : y ∈ A
            · exact Or.inr ⟨⟨x, hx, hxB⟩, ⟨y, hy, fun h => hyn ⟨hyA, h⟩⟩⟩
            · exact Or.inl ⟨⟨x, hx, hxA⟩, ⟨y, hy, hyA⟩⟩
          rw [if_neg h1, if_pos h2]
          rcases this with h | h
          · rw [if_pos h]; split_ifs <;> omega
          · rw [if_pos h]; split_ifs <;> omega
        · rw [if_neg h1, if_neg h2]; split_ifs <;> omega
    exact_mod_cast this
