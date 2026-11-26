-- Prove2me | solution 1 for MellinDuality.parSign_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:43.735701+00:00
-- url     : https://prove2.me/submissions/a66747db-7538-4571-b2c2-4b7da9f8bac8

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
public import Theorems.Thm_MellinDuality_neg_one_pow_sub

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : parSign (-x) = -parSign x := by
  unfold parSign
  rw [val_neg_of_ne_zero' hx, neg_one_pow_sub hp2 (ZMod.val_lt x).le]
end MellinDuality
