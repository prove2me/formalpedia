-- Prove2me | solution 1 for MellinDuality.char_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:27.062923+00:00
-- url     : https://prove2.me/submissions/d193f977-764f-4cae-a0e5-bfb24d766ef6

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
public import Theorems.Thm_MellinDuality_quadraticChar_eq_sq


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution {r : ℕ} (hr : (r : ZMod p) ≠ 0) :
    χ r * χ r = ((legendreSym p r : ℤ) : GaussianInt) := by
  rw [← sq, ← quadraticChar_eq_sq hχ hr, legendreSym, Int.cast_natCast]
end MellinDuality
