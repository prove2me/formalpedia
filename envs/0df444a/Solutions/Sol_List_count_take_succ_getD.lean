-- Prove2me | solution 1 for List.count_take_succ_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:38:01.302855+00:00
-- url     : https://prove2.me/submissions/de0d9b52-eba4-415c-a92c-d4c6b2dc4301

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_count_take_succ

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution [DecidableEq α] (l : List α) (x : α) {i : ℕ} (hi : i < l.length)
    (d : α) :
    (l.take (i + 1)).count x = (l.take i).count x + if l.getD i d = x then 1 else 0 := by
  rw [List.count_take_succ l x hi, List.getD_eq_getElem l d hi]
end List
