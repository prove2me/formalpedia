-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.expo_canonicalPerm_inr_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:54:41.082566+00:00
-- url     : https://prove2.me/submissions/2d456f00-62a9-404a-a12e-97ee3a1158cc

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Main
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_expo_inr


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (f : V ≃ Fin n) (u : V) :
    expo f (canonicalPerm f) (Sum.inr u) < n := by
  rw [expo_inr]
  exact (canonicalPerm f u (f u)).isLt
end LeanPool.ListEdgeColoringComplete
