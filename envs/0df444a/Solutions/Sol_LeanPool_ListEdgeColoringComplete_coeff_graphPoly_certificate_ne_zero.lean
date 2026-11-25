-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.coeff_graphPoly_certificate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:23:08.711662+00:00
-- url     : https://prove2.me/submissions/3923a839-c365-46cb-8d74-883884a1face

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_termSign_ne_zero
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_coeff_graphPoly_certificate

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) :
    (graphPoly f).coeff (expo f (canonicalPerm f)) ≠ 0 := by
  rw [coeff_graphPoly_certificate]
  exact termSign_ne_zero _
end LeanPool.ListEdgeColoringComplete
