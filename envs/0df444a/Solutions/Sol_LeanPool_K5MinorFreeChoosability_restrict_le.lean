-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.restrict_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:32.613933+00:00
-- url     : https://prove2.me/submissions/1bb682ed-5d78-4bf3-a78e-1f0ed0ee8d7e

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (G : SimpleGraph W) (s : Set W) : restrict G s ≤ G :=
  fun _ _ h => h.1
end LeanPool.K5MinorFreeChoosability
