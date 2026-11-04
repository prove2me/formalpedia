-- Prove2me | solution 1 for List.length_filter_lt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:10.27814+00:00
-- url     : https://prove2.me/submissions/2d8cbf3b-2873-48ae-874b-c121f03b1455

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
theorem _root_.solution (t : α → ℕ) (z : ℕ) (l : List α) :
    (l.filter fun a => decide (t a < z + 1)).length =
      (l.filter fun a => decide (t a < z)).length +
        (l.filter fun a => decide (t a = z)).length := by
  simp only [← List.countP_eq_length_filter]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, ih, decide_eq_true_eq]
    split_ifs <;> omega
end List
