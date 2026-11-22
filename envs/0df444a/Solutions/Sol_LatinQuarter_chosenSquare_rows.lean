-- Prove2me | solution 1 for LatinQuarter.chosenSquare_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:25.005364+00:00
-- url     : https://prove2.me/submissions/2383d8b8-0013-475b-86c9-02be51bdc9ab

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Rows

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (σ : RowChoices P) :
    ∀ r, Function.Bijective (chosenSquare P L σ r) := by
  classical
  intro r
  exact (hL.1 r).comp ((σ r).subtypeCongr (Equiv.refl _)).bijective
end LatinQuarter
