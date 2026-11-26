-- Prove2me | solution 1 for MellinDuality.G_eq_two_mul_char_two_mul_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:29.768834+00:00
-- url     : https://prove2.me/submissions/c53b3090-d284-434a-84a5-9fd9c3e9f3cc

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_MellinDuality_parSign_neg
public import Theorems.Thm_MellinDuality_sum_univ_eq_sum_half
public import Theorems.Thm_MellinDuality_apply_neg_of_odd
public import Theorems.Thm_MellinDuality_two_ne_zero_zmod
public import Theorems.Thm_MellinDuality_val_two_mul_of_mem_half
public import Theorems.Thm_MellinDuality_sum_mul_two
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
theorem _root_.solution (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R)
    (hψ : ψ (-1) = -1) : G ψ = 2 * ψ 2 * ∑ n ∈ half p, ψ n := by
  unfold G
  rw [sum_mul_two hp2]
  simp only [map_mul]
  simp_rw [mul_assoc (ψ 2)]
  rw [← mul_sum, sum_univ_eq_sum_half hp2 (fun y => ψ y * (parSign (2 * y) : R))
    (by simp [MulChar.map_zero]), mul_sum, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  by_cases hn0 : n = 0
  · subst hn0; simp [MulChar.map_zero]
  · have h2n : (2 * n : ZMod p) ≠ 0 := mul_ne_zero (two_ne_zero_zmod hp2) hn0
    have hs : parSign (2 * n) = 1 := by
      unfold parSign; rw [val_two_mul_of_mem_half hn, pow_mul]; simp
    rw [show (2 : ZMod p) * -n = -(2 * n) by ring, parSign_neg hp2 h2n, hs,
      apply_neg_of_odd ψ hψ]
    push_cast; ring
end MellinDuality
