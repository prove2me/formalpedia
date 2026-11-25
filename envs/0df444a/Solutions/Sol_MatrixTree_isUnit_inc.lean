-- Prove2me | solution 1 for MatrixTree.isUnit_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:20:34.16525+00:00
-- url     : https://prove2.me/submissions/b81fd6a1-660f-401a-bd60-8fdbd71b9a3c

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
theorem _root_.solution {e : Sym2 V} (he : ¬ e.IsDiag) {x : V} (hx : x ∈ e) : IsUnit (inc e x) := by
  rcases mem_iff_tl_or_hd.mp hx with rfl | rfl
  · rw [inc_tl]; exact isUnit_one
  · rw [inc_hd he]; exact isUnit_one.neg
end MatrixTree
