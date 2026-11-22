-- Prove2me | solution 1 for LatinQuarter.chosenSquare_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:40.033536+00:00
-- url     : https://prove2.me/submissions/05b98a04-4629-43f9-b3e1-04cf468dbd0b

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
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) : Function.Injective (chosenSquare P L) := by
  intro σ τ h
  funext r
  apply Equiv.ext
  intro c
  apply Subtype.ext
  apply (hL.1 r).injective
  have he := congrArg (fun M => M r c) h
  simpa only [chosenSquare_free] using he
end LatinQuarter
