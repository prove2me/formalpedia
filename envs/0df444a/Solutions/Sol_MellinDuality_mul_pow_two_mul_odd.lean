-- Prove2me | solution 1 for MellinDuality.mul_pow_two_mul_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:12.286462+00:00
-- url     : https://prove2.me/submissions/9702a799-2bb5-48ff-a40c-71e16edc6536

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_pow_two_mul_apply_neg_one

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) (m : ℕ) :
    (χ * ψ ^ (2 * m)) (-1) = -1 := by
  rw [MulChar.mul_apply, hχ, pow_two_mul_apply_neg_one, mul_one]
end MellinDuality
