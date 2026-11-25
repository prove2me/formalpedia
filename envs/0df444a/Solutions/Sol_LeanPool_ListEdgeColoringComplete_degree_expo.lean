-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.degree_expo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:47:43.724409+00:00
-- url     : https://prove2.me/submissions/2db60627-963f-4929-b7d0-e23a37e58d49

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
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) :
    (expo f P).degree = Fintype.card V * ∑ k : Fin n, (k : ℕ) := by
  simp only [expo, map_sum, Finsupp.degree_single]
  rw [Finset.sum_congr rfl fun u _ => Equiv.sum_comp (P u) (fun k : Fin n => (k : ℕ))]
  simp
end LeanPool.ListEdgeColoringComplete
