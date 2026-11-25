-- Prove2me | solution 1 for KneserColouring.maxCol_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:17.637822+00:00
-- url     : https://prove2.me/submissions/03e17bdd-3b0b-4dd3-bc81-b16e2c3ef6e6

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
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q) {B B' : Finset (Fin n)}
    (h : B ⊆ B') : maxCol c B ≤ maxCol c B' :=
  Finset.sup_mono (powersetCard_mono h)
end KneserColouring
