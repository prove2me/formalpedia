-- Prove2me | solution 1 for KneserColouring.eq_of_suppCard_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:29.222099+00:00
-- url     : https://prove2.me/submissions/117fe60d-a7ec-430f-9c9a-2274d25288ae

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_supp_mono

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
variable {x y : Fin n → SignType} (hxy : ∀ i, x i ≠ 0 → x i = y i)
include hxy
namespace KneserColouring
theorem _root_.solution (h : suppCard x = suppCard y) : x = y := by
  have hs := eq_of_subset_of_card_le (supp_mono hxy) (by unfold suppCard at h; omega)
  funext i
  by_cases hi : x i = 0
  · have : i ∉ univ.filter (fun i => y i ≠ 0) := by
      rw [← hs]
      simp [hi]
    simp only [mem_filter, mem_univ, true_and, not_not] at this
    rw [hi, this]
  · exact hxy i hi
end KneserColouring
