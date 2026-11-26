-- Prove2me | solution 1 for MellinDuality.exponent_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:31.415491+00:00
-- url     : https://prove2.me/submissions/13997e65-7cba-48cf-8a53-ba914a15c872

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_fam_one_eq_bandSumPow
public import Theorems.Thm_MellinDuality_mellin_inversion
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
theorem _root_.solution (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) :
    bandSumPow χ (2 * m) = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  rw [← fam_one_eq_bandSumPow hp2 χ (by omega), mellin_inversion hp2 χ hχ m one_ne_zero]
  simp only [map_one, one_mul]
end MellinDuality
