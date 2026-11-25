-- Prove2me | solution 1 for KneserColouring.suppCard_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:23.39602+00:00
-- url     : https://prove2.me/submissions/734e3aa2-79e3-49ae-88cb-5dc8c8070e5c

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
theorem _root_.solution : suppCard x ≤ suppCard y := card_le_card (supp_mono hxy)
end KneserColouring
