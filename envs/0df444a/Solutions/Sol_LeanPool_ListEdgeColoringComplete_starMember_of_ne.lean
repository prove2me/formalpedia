-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.starMember_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:42:59.548013+00:00
-- url     : https://prove2.me/submissions/ce6b6a4b-e3a6-40ac-b34a-8d38597c8ac7

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
theorem _root_.solution (f : V ≃ Fin n) {u w : V} (h : w ≠ u) :
    starMember f u (f w) = Sum.inl ⟨s(u, w), by simp [h.symm]⟩ := by
  simp [starMember, h]
end LeanPool.ListEdgeColoringComplete
