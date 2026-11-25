-- Prove2me | solution 1 for MatrixTree.inc_mul_inc_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:20:37.676616+00:00
-- url     : https://prove2.me/submissions/88a83a5a-a13c-4213-8e15-6425136559a7

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_mem_iff_tl_or_hd
public import Theorems.Thm_MatrixTree_inc_tl
public import Theorems.Thm_MatrixTree_inc_hd

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
variable [DecidableEq V]
namespace MatrixTree
theorem _root_.solution {e : Sym2 V} (he : ¬ e.IsDiag) {x y : V} (hxy : x ≠ y) (hx : x ∈ e)
    (hy : y ∈ e) : inc e x * inc e y = -1 := by
  rcases mem_iff_tl_or_hd.mp hx with rfl | rfl <;> rcases mem_iff_tl_or_hd.mp hy with rfl | rfl
  · exact absurd rfl hxy
  · rw [inc_tl, inc_hd he]; norm_num
  · rw [inc_tl, inc_hd he]; norm_num
  · exact absurd rfl hxy
end MatrixTree
