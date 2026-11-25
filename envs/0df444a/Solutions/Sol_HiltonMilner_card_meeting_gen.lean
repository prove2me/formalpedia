-- Prove2me | solution 1 for HiltonMilner.card_meeting_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:10:57.12715+00:00
-- url     : https://prove2.me/submissions/d28bb061-14f8-4ff5-b379-9efef9986cba

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Definitions.Def_HiltonMilnerLib_HiltonMilner

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {α : Type*} [DecidableEq α] {Y B : Finset α} (hBY : B ⊆ Y) (r : ℕ) :
    #((powersetCard r Y).filter (fun D => (D ∩ B).Nonempty)) =
      (#Y).choose r - (#Y - #B).choose r := by
  have h1 := card_filter_add_card_filter_not (s := powersetCard r Y)
    (fun D => (D ∩ B).Nonempty)
  have h2 : (powersetCard r Y).filter (fun D => ¬ (D ∩ B).Nonempty) = powersetCard r (Y \ B) := by
    ext D
    simp only [mem_filter, mem_powersetCard, not_nonempty_iff_eq_empty, subset_sdiff]
    constructor
    · rintro ⟨⟨hDY, hD⟩, hDB⟩
      exact ⟨⟨hDY, disjoint_iff_inter_eq_empty.2 hDB⟩, hD⟩
    · rintro ⟨⟨hDY, hdis⟩, hD⟩
      exact ⟨⟨hDY, hD⟩, disjoint_iff_inter_eq_empty.1 hdis⟩
  rw [h2, card_powersetCard, card_sdiff_of_subset hBY, card_powersetCard] at h1
  omega
end HiltonMilner
