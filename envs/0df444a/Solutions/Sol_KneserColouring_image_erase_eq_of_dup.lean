-- Prove2me | solution 1 for KneserColouring.image_erase_eq_of_dup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:33.146477+00:00
-- url     : https://prove2.me/submissions/ed0bbe2a-c80d-4c35-955f-1c8795d0fbe1

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
theorem _root_.solution {α : Type*} [DecidableEq α] {s : Finset α} {ℓ : α → ℤ} {j j' : α}
    (hj' : j' ∈ s) (hne : j' ≠ j) (heq : ℓ j' = ℓ j) : (s.erase j).image ℓ = s.image ℓ := by
  apply Subset.antisymm (image_subset_image (erase_subset j s))
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
  by_cases haj : a = j
  · subst haj
    exact mem_image.2 ⟨j', mem_erase.2 ⟨hne, hj'⟩, heq⟩
  · exact mem_image_of_mem ℓ (mem_erase.2 ⟨haj, ha⟩)
end KneserColouring
