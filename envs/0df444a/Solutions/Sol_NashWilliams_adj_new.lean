-- Prove2me | solution 1 for NashWilliams.adj_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:41:01.797481+00:00
-- url     : https://prove2.me/submissions/d8db1e38-6dba-4e03-95cc-da0bab6023aa

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}
namespace NashWilliams
theorem _root_.solution {F : SimpleGraph V} {x y u v a b : V}
    (h : (F.deleteEdges {s(x, y)} ⊔ edge u v).Adj a b) :
    (F.Adj a b ∧ s(a, b) ≠ s(x, y)) ∨ s(a, b) = s(u, v) := by
  rcases h with h | h
  · rw [deleteEdges_adj] at h
    exact Or.inl ⟨h.1, h.2⟩
  · rw [edge_adj] at h
    right
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
end NashWilliams
