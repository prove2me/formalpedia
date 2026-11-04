-- Prove2me | solution 1 for List.length_flatMap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:32.997272+00:00
-- url     : https://prove2.me/submissions/7c8d1f1e-f244-46a3-bdbc-a43d396c1e2d

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
theorem _root_.solution (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  rw [List.length_flatMap]
  simpa using List.sum_le_card_nsmul (l.map fun a => (f a).length) c (by simpa using h)
end List
