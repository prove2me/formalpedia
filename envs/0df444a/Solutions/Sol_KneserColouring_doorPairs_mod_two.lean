-- Prove2me | solution 1 for KneserColouring.doorPairs_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:45.582945+00:00
-- url     : https://prove2.me/submissions/21392fb5-79c9-44fa-8303-c9c1b01d0e66

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Theorems.Thm_KneserColouring_sum_mod_two
public import Theorems.Thm_KneserColouring_card_doorPairs
public import Theorems.Thm_KneserColouring_count_doors
public import Theorems.Thm_KneserColouring_rlab_noComp


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution (lab : (Fin n → SignType) → ℤ) (hNC : NoCompLab lab) {K : ℕ}
    (hK : 1 ≤ K) (hKn : K ≤ n) :
    (doorPairs lab K).card % 2 = altCount lab K % 2 := by
  rw [card_doorPairs, sum_mod_two, altCount, filter_filter]
  congr 2
  apply filter_congr
  intro r _
  constructor
  · rintro ⟨hU, h⟩
    refine ⟨hU, ?_⟩
    have hc := count_doors (range K) (rlab lab r) (nonempty_range_iff.2 (by omega))
      (rlab_noComp hNC hU.1 hKn)
    rw [card_range] at hc
    have hf : (range K).filter (door lab K r) = (range K).filter (fun j =>
        (((range K).erase j).image (rlab lab r)).card + 1 = (range K).card ∧
        IsAlt 0 (((range K).erase j).image (rlab lab r))) := filter_congr (fun _ _ => Iff.rfl)
    rw [hf, card_range] at h
    exact hc.1 h
  · rintro ⟨hU, h⟩
    refine ⟨hU, ?_⟩
    have hc := count_doors (range K) (rlab lab r) (nonempty_range_iff.2 (by omega))
      (rlab_noComp hNC hU.1 hKn)
    rw [card_range] at hc
    have hf : (range K).filter (door lab K r) = (range K).filter (fun j =>
        (((range K).erase j).image (rlab lab r)).card + 1 = (range K).card ∧
        IsAlt 0 (((range K).erase j).image (rlab lab r))) := filter_congr (fun _ _ => Iff.rfl)
    rw [hf, card_range]
    exact hc.2 h
end KneserColouring
