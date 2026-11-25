-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.fullRank_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:15:33.08736+00:00
-- url     : https://prove2.me/submissions/d70f52ee-7fd4-4269-aec0-2d48629f0816

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_ne_blockedRank
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_injective

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (hu : u < n) (hv : v < n) (hw : w < n)
    (h : fullRank n u v = fullRank n u w) : v = w := by
  unfold fullRank at h
  split_ifs at h with h1 h2 h2
  · omega
  · exact absurd h.symm (localRank_ne_blockedRank hu hw h2)
  · exact absurd h (localRank_ne_blockedRank hu hv h1)
  · exact localRank_injective hu hv hw h1 h2 h
end LeanPool.ListEdgeColoringComplete
