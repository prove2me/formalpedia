-- Prove2me | solution 1 for MellinDuality.mellin_quartic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:37.106888+00:00
-- url     : https://prove2.me/submissions/e317aa6f-4642-48a4-9481-b7901c31e5ba

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_fam_one_eq_bandSumPow
public import Theorems.Thm_MellinDuality_mellin_bernoulli
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
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    (hpin : χ 2 = Complex.I) :
    bandSumPow χ 2 = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * Complex.I * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by
  rw [← fam_one_eq_bandSumPow hp2 χ (by norm_num), mellin_bernoulli hp2 χ hχ one_ne_zero, hpin]
  simp only [map_one, one_mul]
end MellinDuality
