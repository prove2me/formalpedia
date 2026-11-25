-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.eval_starPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:47:35.790748+00:00
-- url     : https://prove2.me/submissions/eb3baded-337f-4a2a-bd27-7ad2786f25c5

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
theorem _root_.solution (f : V ≃ Fin n) (u : V) (x : StarVar V → ℚ) :
    eval x (starPoly f u) =
      (Matrix.vandermonde (fun k => x (starMember f u k))).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [starPoly, map_sum, map_mul, eval_C, map_prod, map_pow, eval_X]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [Matrix.vandermonde]
end LeanPool.ListEdgeColoringComplete
