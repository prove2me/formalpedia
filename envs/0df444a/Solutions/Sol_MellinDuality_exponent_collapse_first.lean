-- Prove2me | solution 1 for MellinDuality.exponent_collapse_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:04.594889+00:00
-- url     : https://prove2.me/submissions/fe982b86-cc27-49c6-aaac-ce3849e4543e

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_exponent_collapse_one


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (hm : 1 ≤ m) (hdiv : p - 1 ∣ 2 * m) : 2 * bandSumPow χ (2 * m) = -G χ :=
  exponent_collapse_one hp2 χ hχ hm hdiv
end MellinDuality
