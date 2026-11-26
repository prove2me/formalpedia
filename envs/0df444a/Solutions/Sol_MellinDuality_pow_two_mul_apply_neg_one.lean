-- Prove2me | solution 1 for MellinDuality.pow_two_mul_apply_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:15.100707+00:00
-- url     : https://prove2.me/submissions/cc52e6c1-50b3-4156-b395-19377ae6341a

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_pow_apply_of_ne_zero
public import Theorems.Thm_MellinDuality_apply_neg_one_sq

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (ψ : MulChar (ZMod p) R) (m : ℕ) : (ψ ^ (2 * m)) (-1) = 1 := by
  rw [pow_apply_of_ne_zero ψ _ (neg_ne_zero.2 one_ne_zero), pow_mul, apply_neg_one_sq, one_pow]
end MellinDuality
