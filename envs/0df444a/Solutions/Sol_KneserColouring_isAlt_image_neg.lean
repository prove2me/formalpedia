-- Prove2me | solution 1 for KneserColouring.isAlt_image_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:34.134218+00:00
-- url     : https://prove2.me/submissions/6529ddfa-5ff7-4a87-a187-1640901aea94

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
theorem _root_.solution {s : ℕ} {S : Finset ℤ} (h0 : (0 : ℤ) ∉ S) :
    IsAlt s (S.image (fun a => -a)) ↔ IsAlt (s + 1) S := by
  have hfil : ∀ a, ((S.image (fun a => -a)).filter (fun b => |b| < |-a|)).card =
      (S.filter (fun b => |b| < |a|)).card := by
    intro a
    rw [filter_image, card_image_of_injective _ neg_injective]
    congr 1
    apply filter_congr
    intro b _
    simp [abs_neg]
  unfold IsAlt
  constructor
  · intro h a ha
    have h1 := h (-a) (mem_image_of_mem _ ha)
    rw [hfil] at h1
    have ha0 : a ≠ 0 := fun h' => h0 (h' ▸ ha)
    simp only [Nat.even_iff] at h1 ⊢
    omega
  · intro h a' ha'
    obtain ⟨a, ha, rfl⟩ := mem_image.1 ha'
    have h1 := h a ha
    rw [hfil]
    have ha0 : a ≠ 0 := fun h' => h0 (h' ▸ ha)
    simp only [Nat.even_iff] at h1 ⊢
    omega
end KneserColouring
