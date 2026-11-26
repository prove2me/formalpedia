-- Prove2me | solution 1 for MellinDuality.multiplier_constant_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:06.389175+00:00
-- url     : https://prove2.me/submissions/9acdd1cb-3c6b-44b6-95d1-531bd9710280

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_G_eq_zero_of_even


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = 1) :
    G φ = 0 :=
  G_eq_zero_of_even hp2 φ hφ
end MellinDuality
