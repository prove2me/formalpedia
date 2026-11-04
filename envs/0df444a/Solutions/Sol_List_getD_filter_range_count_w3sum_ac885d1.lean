-- Prove2me | solution 1 for List.getD_filter_range_count_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:11.367444+00:00
-- url     : https://prove2.me/submissions/35983b5d-2019-48f5-bd6a-4f33259ee0e1

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_length_filter_range

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution (q : ℕ → Prop) [DecidablePred q] (n : ℕ) {i : ℕ}
    (hi : i < n) (hq : q i) :
    ((List.range n).filter fun j => decide (q j)).getD (Nat.count q i) 0 = i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [List.getD_append _ _ _ _ (by
        rw [List.length_filter_range]
        exact (Nat.count_lt_count_succ_iff.2 hq).trans_le (Nat.count_monotone q h))]
      exact ih h
    · rw [List.getD_append_right _ _ _ _ (List.length_filter_range q i).le,
        List.length_filter_range, Nat.sub_self]
      simp [hq]
end List
