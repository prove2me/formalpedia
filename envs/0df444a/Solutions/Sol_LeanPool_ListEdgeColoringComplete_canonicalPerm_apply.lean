-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.canonicalPerm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:37:09.69194+00:00
-- url     : https://prove2.me/submissions/e22ce407-438e-4154-b4c2-d02cb02e5d2e

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
theorem _root_.solution (f : V ≃ Fin n) (u : V) (k : Fin n) :
    canonicalPerm f u k = canonicalRow (f u) k := rfl
end LeanPool.ListEdgeColoringComplete
