-- Prove2me | solution 1 for HiltonMilner.cross_bound_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:06:49.433803+00:00
-- url     : https://prove2.me/submissions/186abb1c-e2e6-47fa-8158-713baebc50c6

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {X : Finset ℕ} {a : ℕ} (hX : #X = 2 * a) {𝒜 ℬ : Finset (Finset ℕ)}
    (h𝒜 : 𝒜 ⊆ powersetCard a X) (hℬ : ℬ ⊆ powersetCard a X) (hc : Cross 𝒜 ℬ) :
    #𝒜 + #ℬ ≤ (2 * a).choose a := by
  have himg : 𝒜.image (fun A => X \ A) ⊆ powersetCard a X \ ℬ := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    have hA' := mem_powersetCard.1 (h𝒜 hA)
    refine mem_sdiff.2 ⟨mem_powersetCard.2 ⟨sdiff_subset, ?_⟩, fun hB => ?_⟩
    · rw [card_sdiff_of_subset hA'.1, hX, hA'.2]; omega
    · obtain ⟨w, hw⟩ := hc A hA _ hB
      rw [mem_inter, mem_sdiff] at hw
      exact hw.2.2 hw.1
  have hinj : Set.InjOn (fun A => X \ A) 𝒜 := by
    intro A hA B hB hAB
    have hA' := (mem_powersetCard.1 (h𝒜 hA)).1
    have hB' := (mem_powersetCard.1 (h𝒜 hB)).1
    simp only at hAB
    rw [← Finset.sdiff_sdiff_eq_self hA', ← Finset.sdiff_sdiff_eq_self hB', hAB]
  have := card_le_card himg
  rw [card_image_of_injOn hinj, card_sdiff_of_subset hℬ, card_powersetCard, hX] at this
  have : #ℬ ≤ (2 * a).choose a := by
    have := card_le_card hℬ; rwa [card_powersetCard, hX] at this
  omega
end HiltonMilner
