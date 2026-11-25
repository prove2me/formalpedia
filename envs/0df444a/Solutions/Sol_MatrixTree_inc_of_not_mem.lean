-- Prove2me | solution 1 for MatrixTree.inc_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:07:51.83668+00:00
-- url     : https://prove2.me/submissions/f4e491c0-fd28-4337-a385-6e6d3f759e5f

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_mem_iff_tl_or_hd

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
variable [DecidableEq V]
namespace MatrixTree
theorem _root_.solution {e : Sym2 V} {x : V} (hx : x ∉ e) : inc e x = 0 := by
  rw [mem_iff_tl_or_hd, not_or] at hx
  simp [inc, hx.1, hx.2]
end MatrixTree
