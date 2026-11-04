-- Prove2me | solution 1 for List.sum_flatMap_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:36.855979+00:00
-- url     : https://prove2.me/submissions/40d4d55c-6c06-487b-839d-3f356a30d46f

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
theorem _root_.solution {α β : Type*} (l : List α) (g : α → List β) (F : β → ℤ) :
    ((l.flatMap g).map F).sum = (l.map fun x => ((g x).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih]
end List
