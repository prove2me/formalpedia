-- Prove2me | solution 1 for List.abs_sum_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:52.915572+00:00
-- url     : https://prove2.me/submissions/a5ac908c-38a8-43c6-9753-fa62312c2ce9

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_abs_sum_take_map_le

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) :
    |(l.map f).sum| ≤ l.length * B := by
  have htake := abs_sum_take_map_le l f h l.length
  rwa [← List.length_map (f := f), List.take_length, List.length_map] at htake
end List
