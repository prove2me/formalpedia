-- Prove2me | solution 1 for MellinDuality.exponent_family_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:01.79508+00:00
-- url     : https://prove2.me/submissions/8a5f7ae4-eb07-44a0-9a4b-05a7cb4ba8c3

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_exponent_family


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) :
    bandSumPow χ (2 * m) = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, G ψ⁻¹ * G (χ * ψ ^ (2 * m)) :=
  exponent_family hp2 χ hχ hm
end MellinDuality
