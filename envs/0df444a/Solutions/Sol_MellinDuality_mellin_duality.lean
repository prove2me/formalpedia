-- Prove2me | solution 1 for MellinDuality.mellin_duality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:25.129914+00:00
-- url     : https://prove2.me/submissions/95935990-0370-4fde-9f1b-af795970ce9e

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_mellin_forward


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1)
    (m : ℕ) : 2 * ∑ a, ψ⁻¹ a * fam χ (2 * m) a = G ψ⁻¹ * G (χ * ψ ^ (2 * m)) :=
  mellin_forward hp2 χ ψ hχ m
end MellinDuality
