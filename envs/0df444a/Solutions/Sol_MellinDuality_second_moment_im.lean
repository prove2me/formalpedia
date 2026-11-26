-- Prove2me | solution 1 for MellinDuality.second_moment_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:22.297341+00:00
-- url     : https://prove2.me/submissions/011ac209-e665-4c09-adda-36eca1f24b9d

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_hp2_of
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_ne_zero_of_mem_fiber
public import Theorems.Thm_MellinDuality_sum_fiber_mul
public import Theorems.Thm_MellinDuality_char_mul_char_inv
public import Theorems.Thm_MellinDuality_sum_fiber_neg
public import Theorems.Thm_MellinDuality_coset_lemma
public import Theorems.Thm_MellinDuality_gi_sq
public import Theorems.Thm_MellinDuality_parSign_neg


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
theorem _root_.solution :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).im ^ 2 =
      ∑ d ∈ fiber χ 1, multCorr (fiber χ gi) d * multCorr (fiber χ 1) (d ^ 2) := by
  set F1 := fiber χ 1
  set Fi := fiber χ gi
  have hp2 := hp2_of hp8
  have hinner : ∀ u ∈ Fi, ∀ v ∈ Fi,
      ∑ a ∈ F1, parSign (a * u ^ 2) * parSign (a * v ^ 2) = multCorr F1 ((v * u⁻¹) ^ 2) := by
    intro u hu v hv
    have hu0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hu
    have hv0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hv
    have he0 : (v * u⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hv0 (inv_ne_zero hu0))
    have h := sum_fiber_mul (χ := χ) (fun b => parSign b * parSign ((v * u⁻¹) ^ 2 * b)) 1
      (pow_ne_zero 2 hu0) (char_mul_char_inv (pow_ne_zero 2 hu0))
    rw [map_pow, mem_fiber.1 hu, gi_sq, one_mul] at h
    rw [multCorr, ← (show ∑ b ∈ fiber χ (-1), parSign b * parSign ((v * u⁻¹) ^ 2 * b) =
        ∑ b ∈ F1, parSign b * parSign ((v * u⁻¹) ^ 2 * b) from ?_), ← h]
    · refine sum_congr rfl fun a _ => ?_
      congr 2; field_simp
    · rw [sum_fiber_neg hp8 hχ]
      refine sum_congr rfl fun b hb => ?_
      have hb0 := ne_zero_of_mem_fiber one_ne_zero hb
      rw [mul_neg, parSign_neg hp2 hb0, parSign_neg hp2 (mul_ne_zero he0 hb0)]
      ring
  have hshift : ∀ u ∈ Fi, ∑ v ∈ Fi, parSign v * multCorr F1 ((v * u⁻¹) ^ 2) =
      ∑ d ∈ F1, parSign (d * u) * multCorr F1 (d ^ 2) := by
    intro u hu
    have hu0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hu
    have h := sum_fiber_mul (χ := χ) (fun v => parSign v * multCorr F1 ((v * u⁻¹) ^ 2)) 1
      hu0 (char_mul_char_inv hu0)
    rw [mem_fiber.1 hu, one_mul] at h
    rw [← h]
    refine sum_congr rfl fun d _ => ?_
    congr 3; field_simp
  calc ∑ a ∈ F1, (fam χ 2 a).im ^ 2
      = ∑ a ∈ F1, ∑ u ∈ Fi, ∑ v ∈ Fi,
          parSign u * parSign v * (parSign (a * u ^ 2) * parSign (a * v ^ 2)) := by
        refine sum_congr rfl fun a _ => ?_
        rw [(coset_lemma hp8 hχ a).2, sq, sum_mul_sum]
        exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
    _ = ∑ u ∈ Fi, ∑ v ∈ Fi, parSign u * parSign v * multCorr F1 ((v * u⁻¹) ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun u hu => ?_
        rw [sum_comm]
        refine sum_congr rfl fun v hv => ?_
        rw [← mul_sum, hinner u hu v hv]
    _ = ∑ u ∈ Fi, ∑ d ∈ F1, parSign u * parSign (d * u) * multCorr F1 (d ^ 2) := by
        refine sum_congr rfl fun u hu => ?_
        simp_rw [mul_assoc (parSign u)]
        rw [← mul_sum, ← mul_sum, hshift u hu]
    _ = ∑ d ∈ F1, multCorr Fi d * multCorr F1 (d ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun d _ => ?_
        rw [← sum_mul]; rfl
end MellinDuality
