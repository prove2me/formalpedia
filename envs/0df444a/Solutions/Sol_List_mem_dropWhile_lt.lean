-- Prove2me | solution 1 for List.mem_dropWhile_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:13.341196+00:00
-- url     : https://prove2.me/submissions/65e24de8-4605-48ce-97cf-935d426a712e

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
theorem _root_.solution {a c : α} {l : List α} (h : l.Pairwise (· < ·)) :
    (c ∈ l.dropWhile fun c => c < a) ↔ c ∈ l ∧ a ≤ c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    -- If `x < a`, then `x` is skipped. Otherwise nothing is skipped, and `xs` lies above `x ≥ a`.
    grind [List.dropWhile_cons, List.pairwise_cons]
end List
