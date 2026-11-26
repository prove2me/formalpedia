-- Prove2me | solution 1 for MellinDuality.second_moment_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:12.914803+00:00
-- url     : https://prove2.me/submissions/4736ee07-31ae-4fc8-a2c8-8bdf0b1bb648

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_ne_zero_of_mem_fiber
public import Theorems.Thm_MellinDuality_sum_fiber_mul
public import Theorems.Thm_MellinDuality_char_mul_char_inv
public import Theorems.Thm_MellinDuality_coset_lemma

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
    ∑ a ∈ fiber χ 1, (fam χ 2 a).re ^ 2 =
      ∑ d ∈ fiber χ 1, multCorr (fiber χ 1) d * multCorr (fiber χ 1) (d ^ 2) := by
  set F1 := fiber χ 1
  have hinner : ∀ u ∈ F1, ∀ v : ZMod p,
      ∑ a ∈ F1, parSign (a * u ^ 2) * parSign (a * v ^ 2) = multCorr F1 ((v * u⁻¹) ^ 2) := by
    intro u hu v
    have hu0 := ne_zero_of_mem_fiber one_ne_zero hu
    have h := sum_fiber_mul (χ := χ) (fun b => parSign b * parSign ((v * u⁻¹) ^ 2 * b)) 1
      (pow_ne_zero 2 hu0) (char_mul_char_inv (pow_ne_zero 2 hu0))
    rw [map_pow, mem_fiber.1 hu, one_pow, mul_one] at h
    rw [multCorr, ← h]
    refine sum_congr rfl fun a _ => ?_
    congr 2; field_simp
  have hshift : ∀ u ∈ F1, ∑ v ∈ F1, parSign v * multCorr F1 ((v * u⁻¹) ^ 2) =
      ∑ d ∈ F1, parSign (d * u) * multCorr F1 (d ^ 2) := by
    intro u hu
    have hu0 := ne_zero_of_mem_fiber one_ne_zero hu
    have h := sum_fiber_mul (χ := χ) (fun v => parSign v * multCorr F1 ((v * u⁻¹) ^ 2)) 1
      hu0 (char_mul_char_inv hu0)
    rw [mem_fiber.1 hu, mul_one] at h
    rw [← h]
    refine sum_congr rfl fun d _ => ?_
    congr 3; field_simp
  calc ∑ a ∈ F1, (fam χ 2 a).re ^ 2
      = ∑ a ∈ F1, ∑ u ∈ F1, ∑ v ∈ F1,
          parSign u * parSign v * (parSign (a * u ^ 2) * parSign (a * v ^ 2)) := by
        refine sum_congr rfl fun a _ => ?_
        rw [(coset_lemma hp8 hχ a).1, sq, sum_mul_sum]
        exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
    _ = ∑ u ∈ F1, ∑ v ∈ F1, parSign u * parSign v * multCorr F1 ((v * u⁻¹) ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun u hu => ?_
        rw [sum_comm]
        refine sum_congr rfl fun v _ => ?_
        rw [← mul_sum, hinner u hu v]
    _ = ∑ u ∈ F1, ∑ d ∈ F1, parSign u * parSign (d * u) * multCorr F1 (d ^ 2) := by
        refine sum_congr rfl fun u hu => ?_
        simp_rw [mul_assoc (parSign u)]
        rw [← mul_sum, ← mul_sum, hshift u hu]
    _ = ∑ d ∈ F1, multCorr F1 d * multCorr F1 (d ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun d _ => ?_
        rw [← sum_mul]; rfl
end MellinDuality
