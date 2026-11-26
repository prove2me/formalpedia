-- Prove2me | solution 1 for MellinDuality.mellin_duality_quartic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:39.701385+00:00
-- url     : https://prove2.me/submissions/c32de8ac-cb41-4ef1-b33f-0e0fb7977cc0

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_mellin_quartic


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    (hpin : χ 2 = Complex.I) :
    bandSumPow χ 2 = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * Complex.I * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) :=
  mellin_quartic hp2 χ hχ hpin
end MellinDuality
