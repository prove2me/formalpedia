-- Prove2me | solution 1 for LatinQuarter.det_eq_matching_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:40.514255+00:00
-- url     : https://prove2.me/submissions/c0393c7c-f995-4323-a950-e3735125a4ca

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions


attribute [local simp] LatinQuarter.chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_clue
attribute [local simp] LatinQuarter.chosenSquare_one

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {R ι : Type*} [CommRing R] [CharP R 2]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    M.det = ∑ σ : Equiv.Perm ι, ∏ i, M i (σ i) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  have hs : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h, CharTwo.neg_eq]
  rw [hs, one_mul]
  rfl
end LatinQuarter
