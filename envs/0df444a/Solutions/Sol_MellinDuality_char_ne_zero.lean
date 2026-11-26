-- Prove2me | solution 1 for MellinDuality.char_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:04.635964+00:00
-- url     : https://prove2.me/submissions/0d4c309e-8cb4-4be4-8381-0426d2b98104

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_quartic_values


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8
namespace MellinDuality
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : χ x ≠ 0 := by
  rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide
end MellinDuality
