-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.termSign_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:47:50.183724+00:00
-- url     : https://prove2.me/submissions/d6f1c8b6-ef8d-48ae-871e-b4320e84a03a

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
omit [DecidableEq V]
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (P : V → Equiv.Perm (Fin n)) : termSign P ≠ 0 := by
  unfold termSign
  rw [Finset.prod_ne_zero_iff]
  intro u _
  rcases Int.units_eq_one_or (Equiv.Perm.sign (P u)) with h | h <;> simp [h]
end LeanPool.ListEdgeColoringComplete
