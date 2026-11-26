-- Prove2me | solution 1 for MellinDuality.exponent_collapse_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:44.500503+00:00
-- url     : https://prove2.me/submissions/76dbabf3-d40a-4fa7-96bb-89b9c160362f

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_fam_eq
public import Theorems.Thm_MellinDuality_fam_one_eq_bandSumPow
public import Theorems.Thm_MellinDuality_G_eq_two_mul_half
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
theorem _root_.solution (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) (hdiv : p - 1 ∣ 2 * m) : 2 * bandSumPow χ (2 * m) = -G χ := by
  rw [← fam_one_eq_bandSumPow hp2 χ (by omega), fam_eq, G_eq_two_mul_half hp2 χ hχ, ← neg_mul,
    mul_sum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · obtain ⟨j, hj⟩ := hdiv
    have h1 : (1 : ZMod p) * n ^ (2 * m) = 1 := by
      rw [one_mul, hj, pow_mul, ZMod.pow_card_sub_one_eq_one hn, one_pow]
    have hs : parSign (1 : ZMod p) = -1 := by
      unfold parSign; rw [ZMod.val_one]; norm_num
    rw [h1, hs]; push_cast; ring
end MellinDuality
