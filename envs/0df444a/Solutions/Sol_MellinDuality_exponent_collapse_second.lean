-- Prove2me | solution 1 for MellinDuality.exponent_collapse_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:07.555717+00:00
-- url     : https://prove2.me/submissions/8aabbdf1-6b0a-4ef0-bd03-1c0bffa00df1

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_exponent_collapse_two


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    {m : ℕ} (h4 : p - 1 ∣ 4 * m) (h2 : ¬ p - 1 ∣ 2 * m) :
    2 * bandSumPow χ (2 * m) = -G (χ * quadR p R) :=
  exponent_collapse_two hp2 χ hχ h4 h2
end MellinDuality
