-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.starMember_eq_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:43:12.757788+00:00
-- url     : https://prove2.me/submissions/798686c2-018b-48c2-9998-0b6022e31bd6

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
theorem _root_.solution (f : V ≃ Fin n) (u w : V) (k : Fin n) :
    starMember f u k = Sum.inr w ↔ u = w ∧ k = f u := by
  unfold starMember
  split_ifs with h
  · simp only [Sum.inr.injEq]
    constructor
    · rintro rfl; exact ⟨rfl, by rw [← h]; simp⟩
    · rintro ⟨rfl, -⟩; rfl
  · simp only [false_iff, not_and]
    rintro rfl rfl
    simp at h
end LeanPool.ListEdgeColoringComplete
