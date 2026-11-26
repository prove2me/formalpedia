-- Prove2me | solution 1 for MellinDuality.gamma_bernoulli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:13.087803+00:00
-- url     : https://prove2.me/submissions/cdfa1eb8-cab8-4c23-b828-13371f7c44bb

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_hp2_of
public import Theorems.Thm_MellinDuality_quartic_odd
public import Theorems.Thm_MellinDuality_G_eq_two_gamma
public import Theorems.Thm_MellinDuality_bernoulli_form


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
namespace MellinDuality
theorem _root_.solution (hpin : χ 2 = gi) : (p : GaussianInt) * gamma χ = (1 - 2 * gi) * T χ := by
  have h := bernoulli_form (hp2_of hp8) χ (quartic_odd hp8 hχ)
  rw [G_eq_two_gamma hp8 hχ, hpin] at h
  apply mul_left_cancel₀ (by decide : (2 : GaussianInt) ≠ 0)
  linear_combination h
end MellinDuality
