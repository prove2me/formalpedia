-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.canonicalRow_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:22:14.661039+00:00
-- url     : https://prove2.me/submissions/7366cad5-3124-4ff7-ab7d-5e5e9aa8ab53

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_fullRank_injective

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution (i : Fin n) : Function.Injective (canonicalRow i) := by
  intro j k h
  exact Fin.ext (fullRank_injective i.isLt j.isLt k.isLt (congrArg Fin.val h))
end LeanPool.ListEdgeColoringComplete
