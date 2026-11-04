-- Prove2me | solution 1 for List.getD_set_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:28.17978+00:00
-- url     : https://prove2.me/submissions/b2cfaff5-746a-4721-bb81-3973c56c7a0f

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
theorem _root_.solution {l : List α} {q : ℕ} (hq : q < l.length) (a d : α) (q' : ℕ) :
    (l.set q a).getD q' d = if q' = q then a else l.getD q' d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd h1.symm h2
  · exact absurd (h3 ▸ hq) (by omega)
  · rfl
end List
