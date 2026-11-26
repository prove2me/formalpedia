-- Prove2me | solution 1 for MellinDuality.exponent_terminal_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:38.490876+00:00
-- url     : https://prove2.me/submissions/35c9faf5-5826-4079-9968-e86f2eb47cb1

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_quartic_terminal


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {m : ℕ} (hm : 1 ≤ m) (h4 : p - 1 ∣ 4 * m) :
    bandSumPow χ (2 * m) = if p - 1 ∣ 2 * m then -gamma χ else -star (gamma χ) :=
  quartic_terminal hp8 hχ hm h4
end MellinDuality
