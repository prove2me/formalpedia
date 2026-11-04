-- Prove2me | solution 1 for List.toFinset_eq_image_of_length_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:06.086506+00:00
-- url     : https://prove2.me/submissions/b6b22348-6a14-4adc-bad2-7d5633a31338

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
theorem _root_.solution [DecidableEq β] (l : List β) (hl : l.Nodup)
    (S : Finset α) (g : α → β)
    (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y) (hcard : l.length = S.card) :
    l.toFinset = S.image g := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := hsub y (List.mem_toFinset.mp hy)
    exact Finset.mem_image_of_mem g hx
  · rw [Finset.card_image_of_injective S hinj, List.toFinset_card_of_nodup hl, hcard]
end List
