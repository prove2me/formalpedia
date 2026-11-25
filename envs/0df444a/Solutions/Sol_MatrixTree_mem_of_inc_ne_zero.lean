-- Prove2me | solution 1 for MatrixTree.mem_of_inc_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:14:58.215986+00:00
-- url     : https://prove2.me/submissions/ff7f23b6-8581-44d0-a4ba-68c40bdda109

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_inc_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
variable [DecidableEq V]
namespace MatrixTree
theorem _root_.solution {e : Sym2 V} {x : V} (hx : inc e x ≠ 0) : x ∈ e := by
  by_contra h; exact hx (inc_of_not_mem h)
end MatrixTree
