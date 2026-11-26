-- Prove2me | solution 1 for MellinDuality.mellin_forward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:44.061411+00:00
-- url     : https://prove2.me/submissions/ee5212db-d4c6-4b6c-b154-1f682410f874

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_pow_apply_of_ne_zero
public import Theorems.Thm_MellinDuality_mul_pow_two_mul_odd
public import Theorems.Thm_MellinDuality_fam_eq
public import Theorems.Thm_MellinDuality_sum_inv_mul_parSign
public import Theorems.Thm_MellinDuality_G_eq_two_mul_half
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
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) (χ ψ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) (m : ℕ) :
    2 * ∑ a, ψ⁻¹ a * fam χ (2 * m) a = G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  have step : ∑ a, ψ⁻¹ a * fam χ (2 * m) a =
      G ψ⁻¹ * ∑ n ∈ half p, (χ * ψ ^ (2 * m)) n * (parSign n : R) := by
    simp_rw [fam_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn : n = 0
    · subst hn; simp [MulChar.map_zero]
    · calc ∑ a, ψ⁻¹ a * (χ n * (parSign n : R) * (parSign (a * n ^ (2 * m)) : R))
          = χ n * (parSign n : R) * ∑ a, ψ⁻¹ a * (parSign (a * n ^ (2 * m)) : R) := by
            rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
        _ = χ n * (parSign n : R) * (ψ (n ^ (2 * m)) * G ψ⁻¹) := by
            rw [sum_inv_mul_parSign ψ (pow_ne_zero _ hn)]
        _ = G ψ⁻¹ * ((χ * ψ ^ (2 * m)) n * (parSign n : R)) := by
            rw [MulChar.mul_apply, pow_apply_of_ne_zero _ _ hn, map_pow]; ring
  rw [step, G_eq_two_mul_half hp2 _ (mul_pow_two_mul_odd χ ψ hχ m)]
  ring
end MellinDuality
