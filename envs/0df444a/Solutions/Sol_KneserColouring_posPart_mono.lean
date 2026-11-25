-- Prove2me | solution 1 for KneserColouring.posPart_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:37.207576+00:00
-- url     : https://prove2.me/submissions/87cebb8a-1f3f-45dc-a975-b19afc3619ef

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
theorem _root_.solution : posPart x ⊆ posPart y := by
  intro i hi
  simp only [posPart, mem_filter, mem_univ, true_and] at hi ⊢
  rw [← hxy i (by rw [hi]; decide), hi]
end KneserColouring
