-- Prove2me | solution 1 for List.sum_take_succ_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:35.978002+00:00
-- url     : https://prove2.me/submissions/1bb1b9fa-c20d-48d0-b4fd-20b9cb02b2cc

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
theorem _root_.solution {M : Type*} [AddMonoid M] (l : List M) (j : ℕ) :
    (l.take (j + 1)).sum = (l.take j).sum + l.getD j 0 := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · rw [List.sum_take_succ l j hj, List.getD_eq_getElem l 0 hj]
  · rw [List.getD_eq_default l 0 hj, List.take_of_length_le hj,
      List.take_of_length_le (Nat.le_succ_of_le hj), add_zero]
end List
