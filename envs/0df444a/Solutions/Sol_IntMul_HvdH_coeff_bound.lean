-- Prove2me | solution 1 for IntMul.HvdH.coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T21:20:40.666701+00:00
-- url     : https://prove2.me/submissions/7ba87f86-0343-4888-8d6a-3363fb83166f

import Mathlib

open Finset

namespace IntMul.HvdH.Kron

/-- Balanced digit extraction: the low digit of `W = c + B W'` with `2|c| < B`, `B` even, is
`(W + B/2) mod B - B/2`. -/
theorem balanced_digit (B : ℤ) (hB : 0 < B) (hBe : Even B) (c W' : ℤ) (hc : 2 * |c| < B) :
    c = (c + B * W' + B / 2) % B - B / 2 := by
  obtain ⟨h, rfl⟩ := hBe
  have hh : (h + h) / 2 = h := by omega
  rw [hh]
  have : (c + (h + h) * W' + h) % (h + h) = c + h := by
    rw [show c + (h + h) * W' + h = (c + h) + (h + h) * W' by ring, Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt
    · have := neg_abs_le c; omega
    · have := le_abs_self c; omega
  rw [this]; ring

/-- Uniqueness of balanced base-`B` expansions (Kronecker unpacking, Lemma 2.5 step (3)). -/
theorem kronecker_unique (B : ℤ) (n : ℕ) (c c' : ℕ → ℤ) (hc : ∀ i, 2 * |c i| < B)
    (hc' : ∀ i, 2 * |c' i| < B)
    (h : ∑ i ∈ range n, c i * B ^ i = ∑ i ∈ range n, c' i * B ^ i) :
    ∀ i < n, c i = c' i := by
  induction n generalizing c c' with
  | zero => intro i hi; omega
  | succ n ih =>
    have hB : 0 < B := by have := hc 0; have := abs_nonneg (c 0); omega
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one] at h
    have hs : ∀ d : ℕ → ℤ, ∑ i ∈ range n, d (i + 1) * B ^ (i + 1) =
        B * ∑ i ∈ range n, d (i + 1) * B ^ i := by
      intro d; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [hs c, hs c'] at h
    have h0 : c 0 = c' 0 := by
      have hd : B ∣ c 0 - c' 0 := ⟨(∑ i ∈ range n, c' (i + 1) * B ^ i) -
          ∑ i ∈ range n, c (i + 1) * B ^ i, by linarith⟩
      have h1 := hc 0; have h2 := hc' 0
      have hlt : |c 0 - c' 0| < B := by
        have := abs_sub (c 0) (c' 0); linarith
      by_contra hne
      have hne' : c 0 - c' 0 ≠ 0 := sub_ne_zero.2 hne
      have := Int.le_of_dvd (abs_pos.2 hne') ((dvd_abs _ _).2 hd)
      linarith
    have htail : ∑ i ∈ range n, c (i + 1) * B ^ i = ∑ i ∈ range n, c' (i + 1) * B ^ i := by
      rw [h0] at h
      have := add_right_cancel h
      exact mul_left_cancel₀ hB.ne' this
    have ih' := ih (fun i => c (i + 1)) (fun i => c' (i + 1)) (fun i => hc _) (fun i => hc' _) htail
    intro i hi
    rcases i with _ | i
    · exact h0
    · exact ih' i (by omega)

/-- Coefficient bound for a product in `ℤ[y]/(y^r+1)` (or `ℤ[y]`): each coefficient of the
(nega)cyclic product is a sum of `r` terms `± a_k b_l`. -/
theorem coeff_bound {r : ℕ} [NeZero r] (a b : ZMod r → ℤ) (M : ℤ) (ha : ∀ k, |a k| ≤ M)
    (hb : ∀ k, |b k| ≤ M) (s : ZMod r → ZMod r → ℤ) (hs : ∀ k j, |s k j| ≤ 1) (j : ZMod r) :
    |∑ k, a k * b (j - k) * s k j| ≤ r * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (ha 0)
  calc |∑ k, a k * b (j - k) * s k j| ≤ ∑ k, |a k * b (j - k) * s k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ZMod r, M ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [abs_mul, abs_mul, sq]
        calc |a k| * |b (j - k)| * |s k j| ≤ M * M * 1 := by
              apply mul_le_mul (mul_le_mul (ha k) (hb _) (abs_nonneg _) hM) (hs k j)
                (abs_nonneg _) (by positivity)
          _ = M * M := mul_one _
    _ = r * M ^ 2 := by simp [ZMod.card]

end IntMul.HvdH.Kron

theorem solution {r : ℕ} [NeZero r] (a b : ZMod r → ℤ) (M : ℤ) (ha : ∀ k, |a k| ≤ M)
    (hb : ∀ k, |b k| ≤ M) (s : ZMod r → ZMod r → ℤ) (hs : ∀ k j, |s k j| ≤ 1) (j : ZMod r) :
    |∑ k, a k * b (j - k) * s k j| ≤ r * M ^ 2 :=
  IntMul.HvdH.Kron.coeff_bound a b M ha hb s hs j
