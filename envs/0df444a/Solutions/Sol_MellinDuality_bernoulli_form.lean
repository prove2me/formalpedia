-- Prove2me | solution 1 for MellinDuality.bernoulli_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:26.760789+00:00
-- url     : https://prove2.me/submissions/acd38659-2db9-4353-8ad3-7e2e21b41321

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
public import Theorems.Thm_MellinDuality_sum_univ_eq_sum_half
public import Theorems.Thm_MellinDuality_apply_neg_of_odd
public import Theorems.Thm_MellinDuality_two_ne_zero_zmod
public import Theorems.Thm_MellinDuality_val_two_mul_of_mem_half
public import Theorems.Thm_MellinDuality_sum_mul_two
public import Theorems.Thm_MellinDuality_G_eq_two_mul_char_two_mul_half
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
theorem _root_.solution (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R) (hψ : ψ (-1) = -1) :
    (p : R) * G ψ = 2 * (1 - 2 * ψ 2) * T ψ := by
  set U := ∑ n ∈ half p, ψ n with hU
  set Th := ∑ n ∈ half p, ψ n * (n.val : R) with hTh
  have ha := G_eq_two_mul_char_two_mul_half hp2 ψ hψ
  have hb : T ψ = 2 * Th - p * U := by
    unfold T
    rw [sum_univ_eq_sum_half hp2 _ (by simp [MulChar.map_zero]), hTh, hU, mul_sum, mul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn0 : n = 0
    · subst hn0; simp [MulChar.map_zero]
    · rw [apply_neg_of_odd ψ hψ, val_neg_of_ne_zero' hn0,
        Nat.cast_sub (ZMod.val_lt n).le]
      ring
  have hc' : ∑ y : ZMod p, ψ y * ((2 * y).val : R) = 4 * Th - p * U := by
    rw [sum_univ_eq_sum_half hp2 (fun y => ψ y * ((2 * y).val : R))
      (by simp [MulChar.map_zero]), hTh, hU, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    by_cases hn0 : n = 0
    · subst hn0; simp [MulChar.map_zero]
    · have h2n : (2 * n : ZMod p) ≠ 0 := mul_ne_zero (two_ne_zero_zmod hp2) hn0
      have hv := val_two_mul_of_mem_half hn
      have hle : 2 * n.val ≤ p := by rw [← hv]; exact (ZMod.val_lt _).le
      rw [show (2 : ZMod p) * -n = -(2 * n) by ring, val_neg_of_ne_zero' h2n, hv,
        apply_neg_of_odd ψ hψ, Nat.cast_sub hle]
      push_cast; ring
  have hc : T ψ = ψ 2 * (4 * Th - p * U) := by
    unfold T
    rw [sum_mul_two hp2, ← hc', mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [map_mul]; ring
  rw [ha]
  linear_combination (-2 : R) * hc + 4 * ψ 2 * hb
end MellinDuality
