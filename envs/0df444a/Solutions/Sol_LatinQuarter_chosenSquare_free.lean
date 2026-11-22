-- Prove2me | solution 1 for LatinQuarter.chosenSquare_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:55.478217+00:00
-- url     : https://prove2.me/submissions/b6462430-c083-4a9c-b67b-dbc73c1f8ef3

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) (r : Fin n) (c : FreeColumn P r) :
    chosenSquare P L σ r c = L r (σ r c) := by
  classical
  simp [chosenSquare]
end LatinQuarter
