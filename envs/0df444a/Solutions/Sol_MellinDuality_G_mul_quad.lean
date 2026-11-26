-- Prove2me | solution 1 for MellinDuality.G_mul_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:38.215195+00:00
-- url     : https://prove2.me/submissions/6e7be9c8-185f-4d18-8ba9-5a96a70a1624

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_quadraticChar_eq_sq
public import Theorems.Thm_MellinDuality_quartic_values
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
omit hp8
namespace MellinDuality
theorem _root_.solution : G (χ * quadR p GaussianInt) = star (G χ) := by
  unfold G
  rw [star_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [star_mul', star_intCast]
  congr 1
  by_cases hx : x = 0
  · subst hx; simp [MulChar.map_zero]
  · have hq := quadraticChar_eq_sq hχ hx
    rw [MulChar.mul_apply]
    simp only [quadR, MulChar.ringHomComp_apply, eq_intCast]
    rw [hq]
    rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide
end MellinDuality
