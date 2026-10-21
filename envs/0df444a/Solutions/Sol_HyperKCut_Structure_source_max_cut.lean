-- Prove2me | solution 1 for HyperKCut.Structure.source_max_cut
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:12:33.477701+00:00
-- url     : https://prove2.me/submissions/19674d21-943f-49b5-b0b8-5b0421fa69fc

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure

namespace HKSmcAux

variable {V : Type} [Fintype V] [DecidableEq V]

theorem card_filter_add_le (E : Multiset (Finset V)) (p q r s : Finset V → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s]
    (h : ∀ e, (if p e then 1 else 0) + (if q e then 1 else 0) ≤
        (if r e then 1 else 0) + (if s e then (1 : ℕ) else 0)) :
    (E.filter p).card + (E.filter q).card ≤ (E.filter r).card + (E.filter s).card := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    have ha := h a
    simp only [Multiset.filter_cons]
    split_ifs at ha ⊢ <;> simp <;> omega

theorem d_submod (H : HyperKCut.Structure.Hypergraph V) (A B : Finset V) :
    d H (A ∪ B) + d H (A ∩ B) ≤ d H A + d H B := by
  classical
  unfold d
  apply card_filter_add_le
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

theorem min_union_inter (H : HyperKCut.Structure.Hypergraph V) (S T U₁ U₂ : Finset V)
    (h₁ : IsMinTerminalCut H S T U₁) (h₂ : IsMinTerminalCut H S T U₂) :
    IsMinTerminalCut H S T (U₁ ∪ U₂) ∧ IsMinTerminalCut H S T (U₁ ∩ U₂) := by
  have tu : IsTerminalCut S T (U₁ ∪ U₂) :=
    ⟨h₁.1.1.trans Finset.subset_union_left, Finset.disjoint_union_left.mpr ⟨h₁.1.2, h₂.1.2⟩⟩
  have ti : IsTerminalCut S T (U₁ ∩ U₂) :=
    ⟨Finset.subset_inter h₁.1.1 h₂.1.1, Disjoint.mono_left Finset.inter_subset_left h₁.1.2⟩
  have a := h₁.2 _ tu
  have b := h₁.2 _ ti
  have c := h₁.2 _ h₂.1
  have c' := h₂.2 _ h₁.1
  have sm := d_submod H U₁ U₂
  refine ⟨⟨tu, fun U' hU' => ?_⟩, ⟨ti, fun U' hU' => ?_⟩⟩
  · have := h₁.2 U' hU'; omega
  · have := h₁.2 U' hU'; omega

end HKSmcAux

open HKSmcAux in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V)
    (S T : Finset V)
    (hST : Disjoint S T) :
    (∃! U : Finset V, IsSourceMaxMinTerminalCut H S T U) ∧
    (∃! U : Finset V, IsMinTerminalCut H S T U ∧
      ∀ U' : Finset V, IsMinTerminalCut H S T U' → U ⊆ U') := by
  classical
  -- a minimum terminal cut exists
  have hcutsne : (Finset.univ.filter (fun U : Finset V => IsTerminalCut S T U)).Nonempty :=
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hST⟩⟩
  obtain ⟨U₀, hU₀, hU₀min⟩ := Finset.exists_min_image _ (fun U => d H U) hcutsne
  have hU₀' : IsMinTerminalCut H S T U₀ := by
    refine ⟨(Finset.mem_filter.mp hU₀).2, fun U' hU' => ?_⟩
    exact hU₀min U' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU'⟩)
  have hminsne : (Finset.univ.filter (fun U : Finset V => IsMinTerminalCut H S T U)).Nonempty :=
    ⟨U₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU₀'⟩⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM, hMmax⟩ := Finset.exists_max_image _ (fun U => U.card) hminsne
    have hM' := (Finset.mem_filter.mp hM).2
    have hsm : IsSourceMaxMinTerminalCut H S T M := by
      refine ⟨hM', fun U' hU' => ?_⟩
      have hu := (min_union_inter H S T M U' hM' hU').1
      have hc := hMmax (M ∪ U') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      have heq : M = M ∪ U' := Finset.eq_of_subset_of_card_le Finset.subset_union_left hc
      rw [heq]
      exact Finset.subset_union_right
    refine ⟨M, hsm, fun U hU => ?_⟩
    exact Finset.Subset.antisymm (hsm.2 U hU.1) (hU.2 M hM')
  · obtain ⟨M, hM, hMmin⟩ := Finset.exists_min_image _ (fun U => U.card) hminsne
    have hM' := (Finset.mem_filter.mp hM).2
    have hsm : IsMinTerminalCut H S T M ∧
        ∀ U' : Finset V, IsMinTerminalCut H S T U' → M ⊆ U' := by
      refine ⟨hM', fun U' hU' => ?_⟩
      have hi := (min_union_inter H S T M U' hM' hU').2
      have hc := hMmin (M ∩ U') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have heq : M ∩ U' = M := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hc
      rw [← heq]
      exact Finset.inter_subset_right
    refine ⟨M, hsm, fun U hU => ?_⟩
    exact Finset.Subset.antisymm (hU.2 M hM') (hsm.2 U hU.1)
