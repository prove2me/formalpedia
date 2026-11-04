-- Prove2me | solution 1 for List.sum_filter_finRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:37.771195+00:00
-- url     : https://prove2.me/submissions/f02d029e-f8a2-4d7c-8851-9e60892c6c15

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
theorem _root_.solution {m : ℕ} (p : Fin m → Prop) [DecidablePred p] (F : Fin m → ℤ) :
    (((List.finRange m).filter fun x => p x).map F).sum = ∑ x ∈ Finset.univ.filter p, F x := by
  rw [← List.sum_toFinset _ ((List.nodup_finRange m).filter _)]
  exact Finset.sum_congr (by ext x; simp) fun _ _ => rfl
end List
