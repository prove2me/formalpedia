-- Prove2me | solution 1 for List.getD_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:23.227+00:00
-- url     : https://prove2.me/submissions/db6f5486-e166-440a-bd05-58e5a9cd323b

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
theorem _root_.solution (l : List α) (a j : ℕ) (d : α) : (l.drop a).getD j d = l.getD (a + j) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
end List
