-- Prove2me | solution 1 for MellinDuality.exponent_collapse_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:06.273005+00:00
-- url     : https://prove2.me/submissions/c2ad0725-2397-4f8c-b8be-7aed33bd1ae2

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_fam_eq
public import Theorems.Thm_MellinDuality_fam_one_eq_bandSumPow
public import Theorems.Thm_MellinDuality_quad_cast_eq_pow
public import Theorems.Thm_MellinDuality_G_eq_two_mul_half
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_odd_p
public import Theorems.Thm_P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
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
    (h4 : p - 1 ∣ 4 * m) (h2 : ¬ p - 1 ∣ 2 * m) :
    2 * bandSumPow χ (2 * m) = -G (χ * quadR p R) := by
  have hpo := odd_p hp2
  have hp3 : 3 ≤ p := by have := hp.out.two_le; obtain ⟨k, hk⟩ := hpo; omega
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at h2
    · exact h
  -- `2m = (p/2) j` with `j` odd, and `p/2` even
  have hh : p - 1 = 2 * (p / 2) := by obtain ⟨k, hk⟩ := hpo; omega
  obtain ⟨j, hj⟩ : p / 2 ∣ 2 * m := by
    rw [hh] at h4; obtain ⟨c, hc⟩ := h4; exact ⟨c, by linarith⟩
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | h
    · exact absurd ⟨i, by rw [hh, hj]; ring⟩ h2
    · exact h
  have hheven : Even (p / 2) := by
    rcases Nat.even_or_odd (p / 2) with h | ⟨k, hk⟩
    · exact h
    · exfalso
      have hcop : Nat.Coprime (p / 2) 2 := by rw [hk]; simp [Nat.coprime_two_right]
      have : p / 2 ∣ m := hcop.dvd_of_dvd_mul_left ⟨j, by linarith⟩
      obtain ⟨c, hc⟩ := this
      exact h2 ⟨c, by rw [hh, hc]; ring⟩
  have hquad_odd : (χ * quadR p R) (-1) = -1 := by
    have hq : quadraticChar (ZMod p) (-1) = 1 := by
      have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
      rw [quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.2 one_ne_zero), ZMod.card,
        hheven.neg_one_pow]
      simp
    simp [quadR, MulChar.mul_apply, MulChar.ringHomComp_apply, hχ, hq]
  rw [← fam_one_eq_bandSumPow hp2 χ (by omega), fam_eq,
    G_eq_two_mul_half hp2 _ hquad_odd, ← neg_mul, mul_sum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · have hq := quadraticChar_dichotomy (F := ZMod p) hn
    have hpow : (1 : ZMod p) * n ^ (2 * m) = ((quadraticChar (ZMod p) n : ℤ) : ZMod p) := by
      rw [one_mul, hj, pow_mul, ← quad_cast_eq_pow hp2]
      rcases hq with h | h <;> rw [h]
      · simp
      · push_cast; exact hjodd.neg_one_pow
    have hs : (parSign (((quadraticChar (ZMod p) n : ℤ) : ZMod p)) : ℤ) =
        -quadraticChar (ZMod p) n := by
      unfold parSign
      rcases hq with h | h <;> rw [h]
      · simp [ZMod.val_one]
      · rw [Int.cast_neg, Int.cast_one, val_neg_of_ne_zero' one_ne_zero, ZMod.val_one]
        have : Even (p - 1) := by rw [hh]; exact even_two_mul _
        rw [this.neg_one_pow]; norm_num
    rw [hpow, hs]
    simp only [quadR, MulChar.mul_apply, MulChar.ringHomComp_apply, eq_intCast]
    push_cast; ring
end MellinDuality
