-- Prove2me | solution 1 for MellinDuality.G_eq_two_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:16.191921+00:00
-- url     : https://prove2.me/submissions/4e659340-4c00-4ff1-adaa-aacf2ddaa2dd

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_mem_fiber
public import Theorems.Thm_MellinDuality_sum_univ_fibers
public import Theorems.Thm_MellinDuality_sigma_neg
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
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
namespace MellinDuality
theorem _root_.solution : G χ = 2 * gamma χ := by
  have hfib : ∀ z : GaussianInt, ∑ x ∈ fiber χ z, χ x * (parSign x : GaussianInt) =
      z * (sigma χ z : GaussianInt) := by
    intro z; unfold sigma; push_cast; rw [mul_sum]
    exact sum_congr rfl fun x hx => by rw [mem_fiber.1 hx]
  unfold G
  rw [sum_univ_fibers hχ _ (by simp [MulChar.map_zero]), hfib, hfib, hfib, hfib,
    sigma_neg hp8 hχ one_ne_zero, sigma_neg hp8 hχ (by decide : gi ≠ 0)]
  unfold gamma
  ext <;> simp [gi] <;> ring
end MellinDuality
