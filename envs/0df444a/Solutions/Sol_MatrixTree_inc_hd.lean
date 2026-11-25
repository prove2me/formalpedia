-- Prove2me | solution 1 for MatrixTree.inc_hd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:12:26.526665+00:00
-- url     : https://prove2.me/submissions/a8d5a52a-76f3-402f-b5b0-7bf757251d2a

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_tl_ne_hd

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
variable [DecidableEq V]
namespace MatrixTree
theorem _root_.solution {e : Sym2 V} (he : ¬ e.IsDiag) : inc e (hd e) = -1 := by
  simp [inc, (tl_ne_hd he).symm]
end MatrixTree
