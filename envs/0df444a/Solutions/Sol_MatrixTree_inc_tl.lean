-- Prove2me | solution 1 for MatrixTree.inc_tl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:56:02.578656+00:00
-- url     : https://prove2.me/submissions/3927842f-5547-4b4a-897c-9fbc72502859

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
variable [DecidableEq V]
namespace MatrixTree
theorem _root_.solution (e : Sym2 V) : inc e (tl e) = 1 := by simp [inc]
end MatrixTree
