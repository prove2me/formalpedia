-- Prove2me | solution 1 for MatrixTree.mem_iff_tl_or_hd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:02:04.732544+00:00
-- url     : https://prove2.me/submissions/81d7ea71-0773-4195-8778-f0583f6e4a66

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
theorem _root_.solution {e : Sym2 V} {x : V} : x ∈ e ↔ x = tl e ∨ x = hd e := by
  conv_lhs => rw [← mk_tl_hd e]
  exact Sym2.mem_iff
end MatrixTree
