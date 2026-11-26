-- Prove2me | solution 1 for MellinDuality.char_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:24.320181+00:00
-- url     : https://prove2.me/submissions/e183b567-2b47-4a2f-80f9-a2ad9f964be2

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
public import Theorems.Thm_MellinDuality_quartic_values


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : χ x * star (χ x) = 1 := by
  rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide
end MellinDuality
