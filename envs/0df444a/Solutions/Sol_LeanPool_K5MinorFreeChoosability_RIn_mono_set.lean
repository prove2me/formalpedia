-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.mono_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:40.879201+00:00
-- url     : https://prove2.me/submissions/7196c213-3a62-4cb0-a294-7a5c913dd848

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_mono

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
namespace LeanPool.K5MinorFreeChoosability.RIn
theorem _root_.solution (h : RIn G s a b) (hs : s ⊆ t) : RIn G t a b := h.mono le_rfl hs
end LeanPool.K5MinorFreeChoosability.RIn
