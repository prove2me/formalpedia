-- Prove2me | solution 1 for KneserColouring.tucker_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:00:03.954715+00:00
-- url     : https://prove2.me/submissions/21013198-04c7-4feb-a553-d566aa3efee3

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_altCount_odd
public import Theorems.Thm_KneserColouring_NoComp_abs_inj
public import Theorems.Thm_KneserColouring_NoComp_ne_zero
public import Theorems.Thm_KneserColouring_pref_ne_zero
public import Theorems.Thm_KneserColouring_rlab_noComp


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {m : ℕ} (lab : (Fin n → SignType) → ℤ)
    (hlab : ∀ x, x ≠ 0 → |lab x| ≤ m) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) (hn : 1 ≤ n) : n ≤ m := by
  have h := altCount_odd lab hanti hNC n hn le_rfl
  obtain ⟨r, hr⟩ : (univ.filter (fun r : Room n => IsUpper n r ∧
      (IsAlt 0 (labSet lab n r) ∨ IsAlt 1 (labSet lab n r)) ∧
      (labSet lab n r).card = n)).Nonempty := by
    rw [← card_pos]
    unfold altCount at h
    omega
  simp only [mem_filter, mem_univ, true_and] at hr
  obtain ⟨hU, -, hcard⟩ := hr
  have hNCS : NoComp (labSet lab n r) := by
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
    exact rlab_noComp hNC hU.1 le_rfl i hi j hj
  have hsub : (labSet lab n r).image (fun a => |a|) ⊆ Icc (1 : ℤ) m := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    have ha0 := hNCS.ne_zero ha
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
    rw [mem_Icc]
    constructor
    · have := abs_pos.2 ha0
      omega
    · exact hlab _ (pref_ne_zero hU.1 le_rfl (mem_range.1 hi))
  have h2 := card_le_card hsub
  rw [card_image_of_injOn (fun a ha b hb hab => hNCS.abs_inj ha hb hab), hcard,
    Int.card_Icc] at h2
  omega
end KneserColouring
