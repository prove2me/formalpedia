-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.totalDegree_graphPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:27:56.02018+00:00
-- url     : https://prove2.me/submissions/291b2674-09a0-4689-92bd-f3ce8e44ba11

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_graphPoly_eq
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_degree_expo
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_coeff_graphPoly_certificate_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).totalDegree = (expo f (canonicalPerm f)).degree := by
  apply le_antisymm
  · rw [graphPoly_eq]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun P _ => ?_)
    refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    change (expo f P).degree = _
    rw [degree_expo, degree_expo]
  · have hm : expo f (canonicalPerm f) ∈ (graphPoly f).support :=
      mem_support_iff.mpr (coeff_graphPoly_certificate_ne_zero f)
    exact le_totalDegree hm
end LeanPool.ListEdgeColoringComplete
