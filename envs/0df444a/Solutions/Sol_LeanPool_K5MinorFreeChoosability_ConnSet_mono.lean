-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.ConnSet.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:16.403794+00:00
-- url     : https://prove2.me/submissions/43e912fc-c2b0-41e7-9828-fa262190ebee

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_mono_graph

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
namespace LeanPool.K5MinorFreeChoosability
namespace ConnSet
theorem _root_.solution {G G' : SimpleGraph W} {s : Set W} (h : ConnSet G s) (hG : G ≤ G') :
    ConnSet G' s :=
  ⟨h.1, fun a ha b hb => (h.2 a ha b hb).mono_graph hG⟩
end ConnSet
end LeanPool.K5MinorFreeChoosability
