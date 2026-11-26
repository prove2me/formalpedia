-- Prove2me | solution 1 for MellinDuality.sum_inv_mul_parSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:18.779512+00:00
-- url     : https://prove2.me/submissions/d30fb1ff-c60b-4021-ba87-5b9410d1edec

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
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
theorem _root_.solution (ψ : MulChar (ZMod p) R) {c : ZMod p} (hc : c ≠ 0) :
    ∑ a, ψ⁻¹ a * (parSign (a * c) : R) = ψ c * G ψ⁻¹ := by
  unfold G
  rw [mul_sum]
  refine Fintype.sum_bijective (· * c) (Equiv.mulRight₀ c hc).bijective _ _ fun a => ?_
  have hcc : ψ c * ψ⁻¹ c = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hc, map_one]
  simp only [map_mul]
  linear_combination (-(ψ⁻¹ a * (parSign (a * c) : R))) * hcc
end MellinDuality
