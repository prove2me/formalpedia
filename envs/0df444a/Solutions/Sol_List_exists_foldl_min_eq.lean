-- Prove2me | solution 1 for List.exists_foldl_min_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:08.163487+00:00
-- url     : https://prove2.me/submissions/f2170a46-ccf4-4f71-968f-1a4a8bc365e2

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
theorem _root_.solution [LinearOrder β] (f : ℕ → β) (m : ℕ) :
    ∃ k ≤ m, (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) = f k := by
  induction m with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk, he⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, he]
    rcases le_total (f k) (f (m + 1)) with h | h
    · exact ⟨k, Nat.le_succ_of_le hk, min_eq_left h⟩
    · exact ⟨m + 1, le_rfl, min_eq_right h⟩
end List
