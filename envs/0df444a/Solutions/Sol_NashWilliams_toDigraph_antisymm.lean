-- Prove2me | solution 1 for NashWilliams.toDigraph_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:28.394065+00:00
-- url     : https://prove2.me/submissions/f9423273-fcad-486a-bc47-63f10bc02913

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_adj_edgeEnds
public import Theorems.Thm_NashWilliams_edge_eq_of_edgeEnds
public import Theorems.Thm_NashWilliams_toDigraph_adj_ends

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
namespace NashWilliams
theorem _root_.solution (o : G.edgeSet → Bool) (a b : V) (h : (toDigraph G o).Adj a b) :
    ¬ (toDigraph G o).Adj b a := by
  rintro ⟨e', he'⟩
  obtain ⟨e, he⟩ := h
  have hab : a ≠ b := by
    obtain ⟨e0, h0 | h0⟩ := toDigraph_adj_ends G ⟨e, he⟩
    · simpa [h0] using G.ne_of_adj (adj_edgeEnds G e0)
    · simpa [h0] using (G.ne_of_adj (adj_edgeEnds G e0)).symm
  have hee : e = e' := by
    refine edge_eq_of_edgeEnds G (a := a) (b := b) ?_ ?_
    · split at he
      · exact Or.inl he
      · exact Or.inr he
    · split at he'
      · exact Or.inr he'
      · exact Or.inl he'
  subst hee
  by_cases ho : o e
  · simp only [ho, ↓reduceIte] at he he'
    rw [he] at he'
    exact hab (Prod.ext_iff.1 he').1
  · simp only [ho, Bool.false_eq_true, ↓reduceIte] at he he'
    rw [he] at he'
    exact hab (Prod.ext_iff.1 he').2
end NashWilliams
