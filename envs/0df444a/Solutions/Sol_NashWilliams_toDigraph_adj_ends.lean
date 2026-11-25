-- Prove2me | solution 1 for NashWilliams.toDigraph_adj_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:11:38.118801+00:00
-- url     : https://prove2.me/submissions/4f3a1de6-6e97-466a-a3b1-d4de23368d8d

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
namespace NashWilliams
theorem _root_.solution {o : G.edgeSet → Bool} {a b : V} (h : (toDigraph G o).Adj a b) :
    ∃ e : G.edgeSet, edgeEnds G e = (a, b) ∨ edgeEnds G e = (b, a) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  split at he
  · exact Or.inl he
  · exact Or.inr he
end NashWilliams
