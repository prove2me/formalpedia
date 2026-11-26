-- Prove2me | solution 1 for MellinDuality.fiber_gi_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:41.877308+00:00
-- url     : https://prove2.me/submissions/d606dcea-dccf-4de2-8ca3-36201a9a738a

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_hp2_of
public import Theorems.Thm_MellinDuality_mem_fiber
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
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
omit hχ
namespace MellinDuality
theorem _root_.solution (hpin : χ 2 = gi) : fiber χ gi = (fiber χ 1).image (2 * ·) := by
  have h2 := two_ne_zero_zmod (hp2_of hp8)
  ext x
  simp only [mem_image, mem_fiber]
  constructor
  · intro hx
    refine ⟨2⁻¹ * x, ?_, by rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]⟩
    have : χ 2 * χ (2⁻¹ * x) = gi := by rw [← map_mul, ← mul_assoc, mul_inv_cancel₀ h2, one_mul, hx]
    rw [hpin] at this
    exact mul_left_cancel₀ (by decide : gi ≠ 0) (this.trans (mul_one gi).symm)
  · rintro ⟨u, hu, rfl⟩; rw [map_mul, hpin, hu, mul_one]
end MellinDuality
