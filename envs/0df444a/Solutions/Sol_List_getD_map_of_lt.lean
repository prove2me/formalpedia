-- Prove2me | solution 1 for List.getD_map_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:27.332341+00:00
-- url     : https://prove2.me/submissions/e9201f96-80c9-4653-8372-b43868c1c07a

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
theorem _root_.solution (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getD_eq_getElem _ _ hi,
    List.getElem_map]
end List
