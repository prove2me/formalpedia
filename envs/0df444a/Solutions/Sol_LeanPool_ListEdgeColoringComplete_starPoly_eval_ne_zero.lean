-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.starPoly_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:53:13.396588+00:00
-- url     : https://prove2.me/submissions/17d0da02-1aeb-444e-85a8-33034c7cca71

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_eval_starPoly

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (f : V ≃ Fin n) (u : V) (x : StarVar V → ℚ)
    (h : eval x (starPoly f u) ≠ 0) :
    Function.Injective (fun k => x (starMember f u k)) := by
  rw [eval_starPoly] at h
  intro k k' hk
  by_contra hne
  exact h (Matrix.det_vandermonde_eq_zero_iff.mpr ⟨k, k', hk, hne⟩)
end LeanPool.ListEdgeColoringComplete
