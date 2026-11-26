-- Prove2me | solution 1 for MellinDuality.mellin_duality_bernoulli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:36.270839+00:00
-- url     : https://prove2.me/submissions/68a27839-ea04-4cdf-9987-fcee8fe14aa4

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_mellin_bernoulli


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ 2 a = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) :=
  mellin_bernoulli hp2 χ hχ ha
end MellinDuality
