-- Prove2me | solution 1 for KneserColouring.negPart_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:42.366786+00:00
-- url     : https://prove2.me/submissions/9720aeb8-099d-4b88-ab0d-ed5b81f20def

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
variable {x y : Fin n → SignType} (hxy : ∀ i, x i ≠ 0 → x i = y i)
include hxy
namespace KneserColouring
theorem _root_.solution : negPart x ⊆ negPart y := by
  intro i hi
  simp only [negPart, mem_filter, mem_univ, true_and] at hi ⊢
  rw [← hxy i (by rw [hi]; decide), hi]
end KneserColouring
