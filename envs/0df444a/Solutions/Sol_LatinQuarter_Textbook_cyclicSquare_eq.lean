-- Prove2me | solution 1 for LatinQuarter.Textbook.cyclicSquare_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:06.068499+00:00
-- url     : https://prove2.me/submissions/6eff4ff7-e920-46f3-b49e-89257f13c058

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution (n : ℕ) : cyclicSquare n = cyclic n := by
  funext r c
  apply Fin.ext
  rfl
end LatinQuarter.Textbook
