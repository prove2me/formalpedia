-- Prove2me | solution 1 for MellinDuality.pair_structure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:34.321808+00:00
-- url     : https://prove2.me/submissions/3bf93632-3fb7-4599-9cd1-8b1c1b55cde7

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
public import Theorems.Thm_MellinDuality_sum_pairs_gcd
public import Theorems.Thm_MellinDuality_bandSum_eq_Icc
public import Theorems.Thm_MellinDuality_mem_Icc_of_mem_pairRange
public import Theorems.Thm_MellinDuality_char_mul_star
public import Theorems.Thm_MellinDuality_char_mul_self
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_hp2_of
public import Theorems.Thm_MellinDuality_natCast_ne_zero_of_mem
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution (hp8 : p % 8 = 5) :
    bandSumPow χ 2 * star (halfSum χ) =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ ab.1 * star (χ ab.2) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab, (eps p (ab.1 * r) : GaussianInt) ∧
      bandSumPow χ 2 * halfSum χ =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ (ab.1 * ab.2 : ℕ) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab,
            ((legendreSym p r : ℤ) : GaussianInt) * (eps p (ab.1 * r) : GaussianInt) ∧
      bandSumPow χ 2 * star (bandSumPow χ 2) =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ ab.1 * star (χ ab.2) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab,
            (eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt) ∧
      bandSumPow χ 2 * bandSumPow χ 2 =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ (ab.1 * ab.2 : ℕ) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab, ((legendreSym p r : ℤ) : GaussianInt) *
            ((eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt)) := by
  have hp2 := hp2_of hp8
  have hC := bandSum_eq_Icc hp2 χ
  have hstarC : star (bandSumPow χ 2) =
      ∑ n ∈ Icc 1 ((p - 1) / 2), star (χ (n : ZMod p)) * (eps p n : GaussianInt) := by
    rw [hC, star_sum]
    exact sum_congr rfl fun n _ => by rw [star_mul', star_intCast]
  have hr0 : ∀ ab ∈ coprimePairs ((p - 1) / 2), ∀ r ∈ pairRange ((p - 1) / 2) ab,
      ((r : ℕ) : ZMod p) ≠ 0 :=
    fun ab _ r hr => natCast_ne_zero_of_mem (mem_Icc_of_mem_pairRange hr)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hC, halfSum, star_sum, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_star hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul, star_mul']
    linear_combination (χ ab.1 * star (χ ab.2) * (eps p (ab.1 * r) : GaussianInt)) * h1
  · rw [hC, halfSum, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_self hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul]
    linear_combination (χ ab.1 * χ ab.2 * (eps p (ab.1 * r) : GaussianInt)) * h1
  · rw [hstarC, hC, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_star hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul, star_mul']
    linear_combination (χ ab.1 * star (χ ab.2) * (eps p (ab.1 * r) : GaussianInt) *
      (eps p (ab.2 * r) : GaussianInt)) * h1
  · rw [hC, sum_mul_sum, sum_pairs_gcd]
    refine sum_congr rfl fun ab hab => ?_
    rw [mul_sum]
    refine sum_congr rfl fun r hr => ?_
    have h1 := char_mul_self hχ (hr0 ab hab r hr)
    simp only [Nat.cast_mul, map_mul]
    linear_combination (χ ab.1 * χ ab.2 * (eps p (ab.1 * r) : GaussianInt) *
      (eps p (ab.2 * r) : GaussianInt)) * h1
end MellinDuality
