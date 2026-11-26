-- Prove2me | solution 1 for MellinDuality.sum_fiber_fam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:33.108969+00:00
-- url     : https://prove2.me/submissions/05025b5c-0e65-4639-b1ee-3d4f4e345727

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_re_sum
public import Theorems.Thm_MellinDuality_im_sum
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_ne_zero_of_mem_fiber
public import Theorems.Thm_MellinDuality_sum_fiber_mul
public import Theorems.Thm_MellinDuality_char_mul_char_inv
public import Theorems.Thm_MellinDuality_sigma_neg
public import Theorems.Thm_MellinDuality_fam_eq_fibers
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_sq
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



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
theorem _root_.solution {c : GaussianInt} (hc0 : c ≠ 0) :
    ∑ a ∈ fiber χ c, fam χ 2 a = (sigma χ c : GaussianInt) * star (gamma χ) := by
  have hinner : ∀ u : ZMod p, u ≠ 0 →
      ∑ a ∈ fiber χ c, parSign (a * u ^ 2) = sigma χ (c * χ (u ^ 2)) := by
    intro u hu
    exact sum_fiber_mul (fun b => parSign b) c (pow_ne_zero 2 hu)
      (char_mul_char_inv (pow_ne_zero 2 hu))
  have hre : ∑ a ∈ fiber χ c, sqCorr (fiber χ 1) a = sigma χ c * sigma χ 1 := by
    unfold sqCorr; rw [sum_comm]
    unfold sigma; rw [mul_comm, sum_mul]
    refine sum_congr rfl fun u hu => ?_
    have hu0 := ne_zero_of_mem_fiber one_ne_zero hu
    rw [← mul_sum, hinner u hu0, map_pow, mem_fiber.1 hu, one_pow, mul_one]
    unfold sigma; ring
  have him : ∑ a ∈ fiber χ c, sqCorr (fiber χ gi) a = -(sigma χ c * sigma χ gi) := by
    unfold sqCorr; rw [sum_comm]
    conv_rhs => unfold sigma
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun u hu => ?_
    have hu0 := ne_zero_of_mem_fiber (by decide : gi ≠ 0) hu
    rw [← mul_sum, hinner u hu0, map_pow, mem_fiber.1 hu, gi_sq, mul_neg_one,
      sigma_neg hp8 hχ hc0]
    simp only [sigma]; ring
  simp_rw [fam_eq_fibers hp8 hχ]
  ext
  · rw [re_sum]; simp [hre, gamma]
  · rw [im_sum]; simp [him, gamma]
end MellinDuality
