-- Prove2me | solution 1 for MatrixTree.tl_ne_hd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:05:55.307908+00:00
-- url     : https://prove2.me/submissions/e0255d63-2572-4ca3-87a3-29ef9934c744

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_mk_tl_hd

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
namespace MatrixTree
theorem _root_.solution {e : Sym2 V} (he : ¬ e.IsDiag) : tl e ≠ hd e := by
  intro h; apply he; rw [← mk_tl_hd e, Sym2.mk_isDiag_iff]; exact h
end MatrixTree
