-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.coeff_graphPoly_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:18:40.337977+00:00
-- url     : https://prove2.me/submissions/9312296b-f3ba-47aa-b88d-36c432e7efe6

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_graphPoly_eq
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_eq_canonicalPerm_of_expo_eq

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).coeff (expo f (canonicalPerm f)) = termSign (canonicalPerm f) := by
  rw [graphPoly_eq, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (canonicalPerm f)]
  · simp
  · intro P _ hP
    exact ite_eq_right_iff.mpr fun h => absurd (eq_canonicalPerm_of_expo_eq f P h) hP
  · simp
end LeanPool.ListEdgeColoringComplete
