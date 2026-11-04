-- Prove2me | solution 1 for List.getD_take_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:24.245766+00:00
-- url     : https://prove2.me/submissions/ce3aab3d-0d86-4cec-9816-cab8326afe11

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
theorem _root_.solution (l : List α) {n j : ℕ} (hj : j < n) (d : α) :
    (l.take n).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
end List
