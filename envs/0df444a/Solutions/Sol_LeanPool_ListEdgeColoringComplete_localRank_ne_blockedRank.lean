-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.localRank_ne_blockedRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:08:20.034798+00:00
-- url     : https://prove2.me/submissions/3109b18a-cc1d-42f9-a6cd-261523d8f85e

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    localRank n u v ≠ blockedRank n u := by
  unfold localRank IsLowEnd targetDegree diagIndex blockedRank
  split_ifs <;> omega
end LeanPool.ListEdgeColoringComplete
