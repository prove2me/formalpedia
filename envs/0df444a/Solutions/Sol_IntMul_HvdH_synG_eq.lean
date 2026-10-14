-- Prove2me | solution 1 for IntMul.HvdH.synG_eq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T01:31:42.353886+00:00
-- url     : https://prove2.me/submissions/43eea96e-fea0-442a-b2cf-0227c6f8a972

import Definitions.Def_IntMul_HvdH_SynFFT

namespace IntMul.HvdH.SynEq
open IntMul.HvdH

lemma yShift_eq (r : ℕ) (m : ℤ) (a : ℕ → ℂ) (c : ℕ) :
    yShift r m a c = (-1 : ℂ) ^ (((c : ℤ) - m) / r) * a (((c : ℤ) - m) % r).toNat := by
  unfold yShift
  split_ifs with h
  · rw [Even.neg_one_zpow (Int.even_iff.mpr h), one_mul]
  · rw [Odd.neg_one_zpow (Int.odd_iff.mpr (by omega)), neg_one_mul]

lemma yShift_comp (r : ℕ) (hr : 0 < r) (m m' : ℤ) (a : ℕ → ℂ) (c : ℕ) :
    yShift r m (fun c' => yShift r m' a c') c = yShift r (m + m') a c := by
  rw [yShift_eq, yShift_eq, yShift_eq]
  set A : ℤ := (c : ℤ) - m
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hi : ((A % r).toNat : ℤ) = A % r := Int.toNat_of_nonneg (Int.emod_nonneg _ hr')
  rw [hi]
  have hA := Int.emod_add_mul_ediv A r
  have e : (c : ℤ) - (m + m') = (A % r - m') + (A / r) * r := by
    simp only [A] at hA ⊢; linarith
  rw [e, Int.add_mul_ediv_right _ _ hr', Int.add_mul_emod_self_right,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

lemma yShift_sub_r (r : ℕ) (hr : 0 < r) (m : ℤ) (n : ℕ) (a : ℕ → ℂ) (c : ℕ) :
    yShift r (m - r * n) a c = (-1 : ℂ) ^ n * yShift r m a c := by
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [yShift_eq, yShift_eq]
  have e : (c : ℤ) - (m - r * n) = ((c : ℤ) - m) + n * r := by ring
  rw [e, Int.add_mul_ediv_right _ _ hr', Int.add_mul_emod_self_right,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
  ring

lemma yShift_zero (r : ℕ) (a : ℕ → ℂ) (c : ℕ) (hc : c < r) : yShift r 0 a c = a c := by
  rw [yShift_eq]
  have h1 : ((c : ℤ) - 0) / r = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h2 : ((c : ℤ) - 0) % r = c := Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1, h2]; simp

lemma yShift_avg (r : ℕ) (m : ℤ) (a b : ℕ → ℂ) (c : ℕ) :
    yShift r m (fun c => (a c + b c) / 2) c = (yShift r m a c + yShift r m b c) / 2 := by
  simp only [yShift_eq]; ring

lemma yShift_hdiff (r : ℕ) (m : ℤ) (a b : ℕ → ℂ) (c : ℕ) :
    yShift r m (fun c => (a c - b c) / 2) c = (yShift r m a c - yShift r m b c) / 2 := by
  simp only [yShift_eq]; ring

lemma split_sum (f : ℕ → ℂ) (e : ℕ) :
    ∑ k ∈ Finset.range (2 ^ (e + 1)), f k = ∑ k ∈ Finset.range (2 ^ e), (f k + f (k + 2 ^ e)) := by
  rw [show 2 ^ (e + 1) = 2 ^ e + 2 ^ e by ring, Finset.sum_range_add, Finset.sum_add_distrib]
  congr 1; apply Finset.sum_congr rfl; intro k _; rw [add_comm]

theorem synG_eq (r : ℕ) (hr : 0 < r) : ∀ e, 2 ^ e ∣ 2 * r → ∀ (u : ℕ × ℕ → ℂ) (j c : ℕ),
    j < 2 ^ e → c < r →
    synG r e u (j, c) = (1 / 2 ^ e : ℂ) * ∑ k ∈ Finset.range (2 ^ e),
      yShift r (-((2 * r / 2 ^ e * j * k : ℕ) : ℤ)) (fun c' => u (k, c')) c
  | 0 => by
    intro _ u j c hj hc
    obtain rfl : j = 0 := by omega
    simp [synG, yShift_zero r _ c hc]
  | e + 1 => by
    intro hdiv u j c hj hc
    obtain ⟨K, hK⟩ := hdiv
    have hK1 : 2 * r / 2 ^ (e + 1) = K := by rw [hK]; exact Nat.mul_div_cancel_left _ (by positivity)
    have hK2 : 2 * r / 2 ^ e = 2 * K := by
      rw [hK, pow_succ, show 2 ^ e * 2 * K = 2 ^ e * (2 * K) by ring]
      exact Nat.mul_div_cancel_left _ (by positivity)
    have hrK : r = 2 ^ e * K := by rw [pow_succ] at hK; linarith
    have hdiv' : 2 ^ e ∣ 2 * r := ⟨2 * K, by rw [hK]; ring⟩
    have ih := synG_eq r hr e hdiv'
    have hp : (2 : ℂ) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
    simp only [synG]
    split_ifs with hpar
    · obtain ⟨l, rfl⟩ : ∃ l, j = 2 * l := ⟨j / 2, by omega⟩
      have hl : 2 * l / 2 = l := by omega
      rw [hl, ih _ l c (by omega) hc, split_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [yShift_avg]
      simp only [hK1, hK2]
      have e1 : (-((2 * K * l * k : ℕ) : ℤ)) = -((K * (2 * l) * k : ℕ) : ℤ) := by push_cast; ring
      have e2 : (-((K * (2 * l) * (k + 2 ^ e) : ℕ) : ℤ)) =
          -((2 * K * l * k : ℕ) : ℤ) - r * (2 * l : ℕ) := by rw [hrK]; push_cast; ring
      rw [e2, yShift_sub_r r hr, e1, pow_mul]
      simp only [neg_one_sq, one_pow, one_mul, pow_succ]
      field_simp; ring
    · obtain ⟨l, rfl⟩ : ∃ l, j = 2 * l + 1 := ⟨j / 2, by omega⟩
      have hl : (2 * l + 1) / 2 = l := by omega
      rw [hl, ih _ l c (by omega) hc, split_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      simp only [hK1, hK2]
      rw [yShift_comp r hr, yShift_hdiff]
      have e1 : (-((2 * K * l * k : ℕ) : ℤ)) + -((K * k : ℕ) : ℤ) =
          -((K * (2 * l + 1) * k : ℕ) : ℤ) := by push_cast; ring
      have e2 : (-((K * (2 * l + 1) * (k + 2 ^ e) : ℕ) : ℤ)) =
          -((K * (2 * l + 1) * k : ℕ) : ℤ) - r * (2 * l + 1 : ℕ) := by rw [hrK]; push_cast; ring
      rw [e2, yShift_sub_r r hr, e1, Odd.neg_one_pow ⟨l, rfl⟩]
      rw [pow_succ]
      field_simp; ring

end IntMul.HvdH.SynEq

open IntMul.HvdH in
theorem solution (r e : ℕ) (hr : 0 < r) (he : 2 ^ e ∣ 2 * r) (u : ℕ × ℕ → ℂ) (j c : ℕ)
    (hj : j < 2 ^ e) (hc : c < r) :
    synG r e u (j, c) = (1 / 2 ^ e : ℂ) * ∑ k ∈ Finset.range (2 ^ e),
      yShift r (-((2 * r / 2 ^ e * j * k : ℕ) : ℤ)) (fun c' => u (k, c')) c :=
  IntMul.HvdH.SynEq.synG_eq r hr e he u j c hj hc
