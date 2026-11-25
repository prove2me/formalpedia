-- Prove2me | solution 1 for MatrixTree.inc_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:20:35.60608+00:00
-- url     : https://prove2.me/submissions/eac96417-db30-4e19-b2cc-9d1d87a7723f

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_mem_iff_tl_or_hd
public import Theorems.Thm_MatrixTree_inc_tl
public import Theorems.Thm_MatrixTree_inc_hd
public import Theorems.Thm_MatrixTree_inc_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
variable [DecidableEq V]
namespace MatrixTree
theorem _root_.solution {e : Sym2 V} (he : ¬ e.IsDiag) (x : V) :
    inc e x * inc e x = if x ∈ e then 1 else 0 := by
  split_ifs with hx
  · rcases mem_iff_tl_or_hd.mp hx with rfl | rfl
    · rw [inc_tl]; norm_num
    · rw [inc_hd he]; norm_num
  · rw [inc_of_not_mem hx, mul_zero]
end MatrixTree
