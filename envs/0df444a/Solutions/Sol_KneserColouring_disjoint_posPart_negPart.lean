-- Prove2me | solution 1 for KneserColouring.disjoint_posPart_negPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:16.869088+00:00
-- url     : https://prove2.me/submissions/798cc795-8902-43d5-97f7-113821b197af

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
namespace KneserColouring
theorem _root_.solution (x : Fin n → SignType) : Disjoint (posPart x) (negPart x) := by
  rw [posPart, negPart, disjoint_filter]
  intro i _ h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)
end KneserColouring
