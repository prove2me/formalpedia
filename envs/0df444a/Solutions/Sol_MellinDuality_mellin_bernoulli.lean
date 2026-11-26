-- Prove2me | solution 1 for MellinDuality.mellin_bernoulli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:25.431266+00:00
-- url     : https://prove2.me/submissions/6588ebe9-78a1-4aab-8fe5-c07b33e1c390

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_pow_apply_of_ne_zero
public import Theorems.Thm_MellinDuality_mul_pow_two_mul_odd
public import Theorems.Thm_MellinDuality_inv_apply_neg_one
public import Theorems.Thm_MellinDuality_p_sub_one_ne_zero
public import Theorems.Thm_MellinDuality_mellin_inversion
public import Theorems.Thm_MellinDuality_G_eq_bern
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_two_ne_zero_zmod
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
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ 2 a = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by
  have h := mellin_inversion hp2 χ hχ 1 ha
  rw [mul_one] at h
  rw [h, mul_sum, mul_sum]
  refine sum_congr rfl fun ψ hψ => ?_
  have hψo : ψ (-1) = -1 := (mem_filter.1 hψ).2
  rw [G_eq_bern hp2 ψ⁻¹ (by rw [inv_apply_neg_one, hψo]),
    G_eq_bern hp2 (χ * ψ ^ 2) (by simpa using mul_pow_two_mul_odd χ ψ hχ 1),
    MulChar.mul_apply, pow_apply_of_ne_zero ψ 2 (two_ne_zero_zmod hp2)]
  field_simp [p_sub_one_ne_zero]
end MellinDuality
