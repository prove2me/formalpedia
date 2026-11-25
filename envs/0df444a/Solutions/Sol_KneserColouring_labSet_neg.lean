-- Prove2me | solution 1 for KneserColouring.labSet_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:04.100941+00:00
-- url     : https://prove2.me/submissions/d08153c5-1cb8-47ef-ad5c-f4060e9a7b11

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
public import Theorems.Thm_KneserColouring_pref_ne_zero
public import Theorems.Thm_KneserColouring_pref_neg


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    {k : ℕ} {t : Fin n → SignType} {ρ : Equiv.Perm (Fin n)} (h : IsRoom k (t, ρ)) (hk : k ≤ n) :
    labSet lab k (-t, ρ) = (labSet lab k (t, ρ)).image (fun a => -a) := by
  rw [labSet, labSet, image_image]
  apply image_congr
  intro i hi
  simp only [Function.comp, rlab]
  rw [pref_neg (t, ρ), hanti _ (pref_ne_zero h hk (mem_range.1 hi))]
end KneserColouring
