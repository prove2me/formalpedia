-- Prove2me | solution 1 for MellinDuality.mellin_duality_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:35.800538+00:00
-- url     : https://prove2.me/submissions/dc067be9-f6aa-46d3-bc34-75c3649193d8

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_mellin_inversion


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) (m : ℕ)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ (2 * m) a = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) :=
  mellin_inversion hp2 χ hχ m ha
end MellinDuality
