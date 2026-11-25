-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.graphPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:36:35.116267+00:00
-- url     : https://prove2.me/submissions/c73a98c2-f51a-4c00-a93f-a72889b57e0f

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
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) :
    graphPoly f = ∑ P : V → Equiv.Perm (Fin n), monomial (expo f P) (termSign P) := by
  unfold graphPoly starPoly
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp only [X_pow_eq_monomial]
  rw [Finset.prod_congr rfl fun u _ => (monomial_sum_one _ _).symm, ← monomial_sum_one,
    C_mul_monomial, mul_one]
  rfl
end LeanPool.ListEdgeColoringComplete
