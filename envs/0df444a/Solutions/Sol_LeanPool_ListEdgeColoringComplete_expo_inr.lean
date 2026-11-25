-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.expo_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:48:34.021162+00:00
-- url     : https://prove2.me/submissions/524aa6d0-bc99-4357-a125-a6ea3347677c

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_starMember_eq_inr

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) (u : V) :
    expo f P (Sum.inr u) = P u (f u) := by
  simp only [expo, Finsupp.finsetSum_apply, Finsupp.single_apply, starMember_eq_inr]
  rw [Fintype.sum_eq_single u, Fintype.sum_eq_single (f u)]
  · simp
  · intro k hk
    simp [hk]
  · intro w hw
    exact Finset.sum_eq_zero fun k _ => by simp [hw]
end LeanPool.ListEdgeColoringComplete
