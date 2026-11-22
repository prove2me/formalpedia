-- Prove2me | solution 1 for LatinQuarter.chosenSquare_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:14.101356+00:00
-- url     : https://prove2.me/submissions/2bd7d63c-060d-4c77-8f51-25be109a3f8f

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions


attribute [local simp] LatinQuarter.chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_clue

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n)) (L : Square n) :
    chosenSquare P L 1 = L := by
  classical
  ext r c
  simp [chosenSquare, Equiv.Perm.subtypeCongr.apply]
end LatinQuarter
