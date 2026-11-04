-- Prove2me | solution 1 for List.sum_take_map_range_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:03.831531+00:00
-- url     : https://prove2.me/submissions/826a0fc8-e784-4954-bbda-534f86362b2d

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_getD_map_range
public import Theorems.Thm_List_sum_take_succ_getD

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution {M : Type*} [AddMonoid M] (f : ℕ → M) {n j : ℕ} (hj : j < n) :
    (((List.range n).map f).take (j + 1)).sum = (((List.range n).map f).take j).sum + f j := by
  rw [sum_take_succ_getD, getD_map_range f hj]
end List
