-- Prove2me | solution 1 for MellinDuality.char_mul_char_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:57.321687+00:00
-- url     : https://prove2.me/submissions/90881921-dd30-477b-919c-5ce6a66209af

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
namespace MellinDuality
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : χ x * χ x⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]
end MellinDuality
