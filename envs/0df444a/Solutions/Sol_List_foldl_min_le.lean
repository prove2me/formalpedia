-- Prove2me | solution 1 for List.foldl_min_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:06.964618+00:00
-- url     : https://prove2.me/submissions/5eafb8f6-731e-4204-9e8d-ca9f8f5ef0b9

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution [LinearOrder β] (f : ℕ → β) (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) ≤ f k := by
  induction m with
  | zero => exact (Nat.le_zero.1 hk ▸ le_rfl : f 0 ≤ f k)
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.le_succ_iff.1 hk with h | rfl
    · exact (min_le_left _ _).trans (ih h)
    · exact min_le_right _ _
end List
