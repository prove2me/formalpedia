-- Prove2me | solution 1 for MellinDuality.multiplier_constant_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:04.387808+00:00
-- url     : https://prove2.me/submissions/280b2cf6-6f72-4057-be46-f48ba2e7aa29

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_G_eq_two_mul_char_two_mul_half
public import Theorems.Thm_MellinDuality_G_eq_two_mul_half


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) :
    G φ = 2 * ∑ n ∈ half p, φ n * (parSign n : R) ∧ G φ = 2 * φ 2 * ∑ n ∈ half p, φ n :=
  ⟨G_eq_two_mul_half hp2 φ hφ, G_eq_two_mul_char_two_mul_half hp2 φ hφ⟩
end MellinDuality
