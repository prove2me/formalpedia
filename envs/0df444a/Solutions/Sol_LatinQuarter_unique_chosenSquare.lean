-- Prove2me | solution 1 for LatinQuarter.unique_chosenSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:17.701968+00:00
-- url     : https://prove2.me/submissions/39d81944-3967-47b4-a65d-32016e4c9469

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_chosenSquare_agrees
public import Theorems.Thm_LatinQuarter_chosenSquare_injective
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions


attribute [local simp] LatinQuarter.chosenSquare_one

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) (σ : RowChoices P)
    (hσ : IsLatin (chosenSquare P L σ)) : σ = 1 := by
  apply chosenSquare_injective P L h.1
  rw [chosenSquare_one]
  exact h.2 _ hσ (chosenSquare_agrees P L σ)
end LatinQuarter
