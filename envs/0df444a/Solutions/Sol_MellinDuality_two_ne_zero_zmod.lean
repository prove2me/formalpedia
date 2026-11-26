-- Prove2me | solution 1 for MellinDuality.two_ne_zero_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:57.966392+00:00
-- url     : https://prove2.me/submissions/3ab4bb50-baab-43b0-b875-2cb212232c99

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
end MellinDuality
