-- Prove2me | solution 1 for List.mem_takeWhile_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:14.253494+00:00
-- url     : https://prove2.me/submissions/ca431aad-2b4e-4da3-a5ac-d9c13e74b73c

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
variable [LinearOrder α]
namespace List
theorem _root_.solution {b c : α} {l : List α} (h : l.Pairwise (· < ·)) :
    (c ∈ l.takeWhile fun c => c < b) ↔ c ∈ l ∧ c < b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    -- If `x < b`, then `x` is taken. Otherwise nothing is taken, and `xs` lies above `x ≥ b`.
    grind [List.takeWhile_cons, List.pairwise_cons]
end List
