-- Prove2me | solution 1 for List.sum_map_eq_sum_of_length_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:38:00.319192+00:00
-- url     : https://prove2.me/submissions/b7fd3687-e9a8-4016-a486-0908b0226cf9

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_toFinset_eq_image_of_length_eq_card

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution {M : Type*} [AddCommMonoid M] (l : List β) (hl : l.Nodup)
    (S : Finset α)
    (g : α → β) (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y)
    (hcard : l.length = S.card) (F : β → M) : (l.map F).sum = ∑ x ∈ S, F (g x) := by
  classical
  rw [← List.sum_toFinset F hl, toFinset_eq_image_of_length_eq_card l hl S g hinj hsub hcard,
    Finset.sum_image fun x _ y _ hxy => hinj hxy]
end List
