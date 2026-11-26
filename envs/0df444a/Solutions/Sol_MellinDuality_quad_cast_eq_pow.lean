-- Prove2me | solution 1 for MellinDuality.quad_cast_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:54.562174+00:00
-- url     : https://prove2.me/submissions/cc0f4739-60b2-4fc4-b323-beae588338de

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (n : ZMod p) :
    ((quadraticChar (ZMod p) n : ℤ) : ZMod p) = n ^ (p / 2) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  simpa [ZMod.card] using quadraticChar_eq_pow_of_char_ne_two' hF n
end MellinDuality
