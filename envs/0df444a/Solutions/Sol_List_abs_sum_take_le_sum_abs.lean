-- Prove2me | solution 1 for List.abs_sum_take_le_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:05.078097+00:00
-- url     : https://prove2.me/submissions/eaf0b74c-673e-433e-b3d7-0b10ea7e47b3

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_abs_sum_le_sum_abs

set_option autoImplicit false
public section
open List
variable {α β : Type*}
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
namespace List
theorem _root_.solution (l : List R) (k : ℕ) :
    |(l.take k).sum| ≤ (l.map fun x => |x|).sum := by
  refine (abs_sum_le_sum_abs _).trans ?_
  refine Sublist.sum_le_sum ((take_sublist k l).map _) fun a ha => ?_
  obtain ⟨x, -, rfl⟩ := mem_map.mp ha
  exact abs_nonneg x
end List
