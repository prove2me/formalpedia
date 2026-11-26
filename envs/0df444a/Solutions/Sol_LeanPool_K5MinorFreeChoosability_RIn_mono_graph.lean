-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.mono_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:52.397741+00:00
-- url     : https://prove2.me/submissions/82272b6f-01ce-4580-aa71-04920ebd310c

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
theorem _root_.solution (h : RIn G s a b) (hG : G ≤ G') : RIn G' s a b := h.mono hG subset_rfl
end LeanPool.K5MinorFreeChoosability.RIn
