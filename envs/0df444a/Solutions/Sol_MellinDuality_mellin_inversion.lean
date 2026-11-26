-- Prove2me | solution 1 for MellinDuality.mellin_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:59.464429+00:00
-- url     : https://prove2.me/submissions/cfd06bc9-4473-4929-b327-6d5e4aa8ea57

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_inv_apply_neg_one
public import Theorems.Thm_MellinDuality_mellin_forward
public import Theorems.Thm_MellinDuality_totient_cast
public import Theorems.Thm_MellinDuality_p_sub_one_ne_zero
public import Theorems.Thm_MellinDuality_sum_oddChars_eq_sum
public import Theorems.Thm_MellinDuality_G_eq_zero_of_even
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
theorem _root_.solution (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) (m : ℕ)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ (2 * m) a = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by
  rw [sum_oddChars_eq_sum _ (fun ψ hψ => by
    rw [G_eq_zero_of_even hp2 ψ⁻¹ (by rw [inv_apply_neg_one, hψ])]; ring)]
  have key : ∑ ψ : DirichletCharacter ℂ p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) =
      2 * ((p : ℂ) - 1) * fam χ (2 * m) a := by
    calc ∑ ψ : DirichletCharacter ℂ p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m))
        = ∑ ψ : DirichletCharacter ℂ p, ∑ b, 2 * fam χ (2 * m) b * (ψ a * ψ⁻¹ b) := by
          refine sum_congr rfl fun ψ _ => ?_
          rw [mul_assoc, ← mellin_forward hp2 χ ψ hχ m, mul_sum, mul_sum]
          exact sum_congr rfl fun b _ => by ring
      _ = ∑ b, 2 * fam χ (2 * m) b * ∑ ψ : DirichletCharacter ℂ p, ψ a * ψ⁻¹ b := by
          rw [sum_comm]; simp_rw [mul_sum]
      _ = ∑ b, 2 * fam χ (2 * m) b * (if b = a then (p : ℂ) - 1 else 0) := by
          refine sum_congr rfl fun b _ => ?_
          congr 1
          by_cases hb : b = 0
          · subst hb
            simp [MulChar.map_zero, Ne.symm ha]
          · have h' : ∀ ψ : DirichletCharacter ℂ p, ψ a * ψ⁻¹ b = ψ b⁻¹ * ψ a := fun ψ => by
              rw [MulChar.inv_apply', mul_comm]
            rw [sum_congr rfl fun ψ _ => h' ψ,
              DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_iff_ne_zero.2 hb) a,
              totient_cast]
      _ = 2 * ((p : ℂ) - 1) * fam χ (2 * m) a := by
          simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]; ring
  rw [key]
  field_simp [p_sub_one_ne_zero]
end MellinDuality
