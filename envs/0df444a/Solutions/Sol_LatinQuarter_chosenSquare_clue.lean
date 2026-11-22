-- Prove2me | solution 1 for LatinQuarter.chosenSquare_clue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:36.840305+00:00
-- url     : https://prove2.me/submissions/05961bd7-91ec-499c-8310-a903cfecbf33

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions


attribute [local simp] LatinQuarter.chosenSquare_free

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) (r c : Fin n) (hc : (r, c) ∈ P) :
    chosenSquare P L σ r c = L r c := by
  classical
  simp [chosenSquare, hc]
end LatinQuarter
