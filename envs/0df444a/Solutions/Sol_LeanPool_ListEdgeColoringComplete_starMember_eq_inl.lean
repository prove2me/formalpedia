-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.starMember_eq_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:53:24.681461+00:00
-- url     : https://prove2.me/submissions/fedc825b-790e-4b68-991b-b0b034b90f8c

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (f : V ≃ Fin n) (u a b : V) (k : Fin n)
    (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    starMember f u k = Sum.inl ⟨s(a, b), hab⟩ ↔
      (u = a ∧ k = f b) ∨ (u = b ∧ k = f a) := by
  have hne : a ≠ b := by simpa using hab
  unfold starMember
  split_ifs with h
  · simp only [false_iff, not_or, not_and]
    constructor
    · rintro rfl rfl; exact hne (by simpa using h.symm)
    · rintro rfl rfl; exact hne (by simpa using h)
  · simp only [Sum.inl.injEq, Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk]
    constructor
    · rintro (⟨rfl, h2⟩ | ⟨rfl, h2⟩)
      · exact Or.inl ⟨rfl, by rw [← h2]; simp⟩
      · exact Or.inr ⟨rfl, by rw [← h2]; simp⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, by simp⟩
      · exact Or.inr ⟨rfl, by simp⟩
end LeanPool.ListEdgeColoringComplete
