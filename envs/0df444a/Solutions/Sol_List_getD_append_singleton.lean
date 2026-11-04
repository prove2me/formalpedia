-- Prove2me | solution 1 for List.getD_append_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:29.104204+00:00
-- url     : https://prove2.me/submissions/0d9a379d-6698-45d9-9cdf-2138f280e2a6

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
theorem _root_.solution (l : List α) (a d : α) :
    (fun e => (l ++ [a]).getD e d) = Function.update (fun e => l.getD e d) l.length a := by
  funext e
  rcases Nat.lt_trichotomy e l.length with he | rfl | he
  · rw [Function.update_of_ne he.ne, List.getD_append _ _ _ _ he]
  · rw [Function.update_self, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
      List.getD_cons_zero]
  · rw [Function.update_of_ne he.ne', List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ he.le]
end List
