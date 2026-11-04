-- Prove2me | solution 1 for List.count_take_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:54.011657+00:00
-- url     : https://prove2.me/submissions/c4bf380d-21b8-42d1-8f90-1c612b986487

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_count_take_succ_getD

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution [DecidableEq α] {l : List α} {i : ℕ} {x : α} (hi : i < l.length) (d : α)
    (hx : l.getD i d = x) : (l.take i).count x < l.count x := by
  have hle : (l.take (i + 1)).count x ≤ l.count x := (List.take_sublist _ _).count_le _
  rw [count_take_succ_getD l x hi d, if_pos hx] at hle
  omega
end List
