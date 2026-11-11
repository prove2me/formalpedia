-- Prove2me | solution 1 for NCQuadLB.nd_le_six_mul
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:29:17.419874+00:00
-- url     : https://prove2.me/submissions/4c09e069-f515-445c-a000-2fa0f26472f3

import Mathlib

theorem nc_choose_mono_aux (S d : ℕ) (hS : 2 * d ≤ S) :
    ∀ j, j ≤ d → S.choose (d - j) ≤ S.choose d := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 : d - (j + 1) < S / 2 := by
      have : d ≤ S / 2 := by omega
      omega
    have h2 := Nat.choose_le_succ_of_lt_half_left h1
    have h3 : d - (j + 1) + 1 = d - j := by omega
    rw [h3] at h2
    exact h2.trans (ih (by omega))

theorem nc_sum_le_aux (n d S : ℕ) (hd : 1 ≤ d)
    (hcount : n ^ d ≤ ∑ k ∈ Finset.range (d + 1), S.choose k) (hn : 2 ≤ n) (hlt : S < 2 * d) :
    n < 4 ∧ d ≤ S := by
  have hsum : ∑ k ∈ Finset.range (d + 1), S.choose k ≤ 2 ^ S := by
    rw [← Nat.sum_range_choose S]
    rcases le_or_gt d S with h | h
    · exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    · apply le_of_eq
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hk'
      apply Nat.choose_eq_zero_of_lt
      simp only [Finset.mem_range] at hk hk'
      omega
  have h2 : n ^ d ≤ 2 ^ S := hcount.trans hsum
  have h3 : 2 ^ d ≤ n ^ d := Nat.pow_le_pow_left hn d
  constructor
  · by_contra hcon
    push Not at hcon
    have : 4 ^ d ≤ n ^ d := Nat.pow_le_pow_left hcon d
    have h4 : 2 ^ S < 4 ^ d := by
      have : (4 : ℕ) ^ d = 2 ^ (2 * d) := by rw [pow_mul]; norm_num
      rw [this]
      exact Nat.pow_lt_pow_right (by norm_num) hlt
    omega
  · have : 2 ^ d ≤ 2 ^ S := h3.trans h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

/-- **Proof of Theorem 4.2, the numerical conclusion** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.8). Let `n ≥ 2`, `d ≥ 1` and let `S`
be a natural number with `n^d ≤ ∑_{k=0}^d (S choose k)`. If `d ≤ S/2` then
`S ≥ nd/(e(d+1)^{1/d}) ≥ (nd)/6`; and in every case `S ≥ (nd)/6`.

**Formalization Note** `S` is any natural number satisfying the counting inequality (for a circuit
computing `Pal_{n,d}`, its number of product gates, by the counting milestone). `d ≤ S/2` is `2d ≤ S`,
`e = Real.exp 1`, `(d+1)^{1/d}` is the real power. `S ≥ (nd)/6` is stated as `nd ≤ 6S` in `ℕ`. -/
theorem solution (n d S : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hcount : n ^ d ≤ ∑ k ∈ Finset.range (d + 1), S.choose k) :
    (2 * d ≤ S →
      ((n : ℝ) * d) / (Real.exp 1 * ((d : ℝ) + 1) ^ ((1 : ℝ) / d)) ≤ S ∧
        ((n : ℝ) * d) / 6 ≤ ((n : ℝ) * d) / (Real.exp 1 * ((d : ℝ) + 1) ^ ((1 : ℝ) / d))) ∧
      n * d ≤ 6 * S := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  set P : ℝ := ((d : ℝ) + 1) ^ ((1 : ℝ) / d) with hP
  have hPpos : 0 < P := by positivity
  have hPd : P ^ d = (d : ℝ) + 1 := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div,
      inv_mul_cancel₀ hdpos.ne', Real.rpow_one]
  have hP2 : P ≤ 2 := by
    have h1 : (d : ℝ) + 1 ≤ 2 ^ d := by
      have : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
      exact_mod_cast this
    by_contra hcon
    push Not at hcon
    have : (2 : ℝ) ^ d < P ^ d := pow_lt_pow_left₀ hcon (by norm_num) (by omega)
    rw [hPd] at this
    linarith
  have hcase : 2 * d ≤ S →
      ((n : ℝ) * d) / (Real.exp 1 * P) ≤ S ∧
        ((n : ℝ) * d) / 6 ≤ ((n : ℝ) * d) / (Real.exp 1 * P) := by
    intro hS
    have hmono : ∑ k ∈ Finset.range (d + 1), S.choose k ≤ (d + 1) * S.choose d := by
      calc ∑ k ∈ Finset.range (d + 1), S.choose k
          ≤ ∑ _k ∈ Finset.range (d + 1), S.choose d := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
            have := nc_choose_mono_aux S d hS (d - k) (by omega)
            have e : d - (d - k) = k := by omega
            rwa [e] at this
        _ = (d + 1) * S.choose d := by simp
    have h1 : n ^ d ≤ (d + 1) * S.choose d := hcount.trans hmono
    have h1R : (n : ℝ) ^ d ≤ ((d : ℝ) + 1) * (S.choose d : ℝ) := by exact_mod_cast h1
    have h2 : (S.choose d : ℝ) ≤ (S : ℝ) ^ d / (Nat.factorial d : ℝ) :=
      Nat.choose_le_pow_div d S
    have hfpos : (0 : ℝ) < (Nat.factorial d : ℝ) := by exact_mod_cast Nat.factorial_pos d
    have h3 : (d : ℝ) ^ d / (Nat.factorial d : ℝ) ≤ Real.exp d :=
      Real.pow_div_factorial_le_exp _ hdpos.le d
    rw [div_le_iff₀ hfpos] at h3
    rw [le_div_iff₀ hfpos] at h2
    have hexp : Real.exp (d : ℝ) = (Real.exp 1) ^ d := by
      rw [← Real.exp_nat_mul]; simp
    rw [hexp] at h3
    have key : ((n : ℝ) * d) ^ d ≤ (P * Real.exp 1 * S) ^ d := by
      rw [mul_pow, mul_pow, mul_pow, hPd]
      calc (n : ℝ) ^ d * (d : ℝ) ^ d
          ≤ (n : ℝ) ^ d * ((Real.exp 1) ^ d * (Nat.factorial d : ℝ)) := by gcongr
        _ = ((n : ℝ) ^ d * (Nat.factorial d : ℝ)) * (Real.exp 1) ^ d := by ring
        _ ≤ (((d : ℝ) + 1) * (S : ℝ) ^ d) * (Real.exp 1) ^ d := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            calc (n : ℝ) ^ d * (Nat.factorial d : ℝ)
                ≤ ((d : ℝ) + 1) * (S.choose d : ℝ) * (Nat.factorial d : ℝ) := by gcongr
              _ = ((d : ℝ) + 1) * ((S.choose d : ℝ) * (Nat.factorial d : ℝ)) := by ring
              _ ≤ ((d : ℝ) + 1) * (S : ℝ) ^ d := by gcongr
        _ = ((d : ℝ) + 1) * (Real.exp 1) ^ d * (S : ℝ) ^ d := by ring
    have hle : (n : ℝ) * d ≤ P * Real.exp 1 * S :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp key
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]; linarith
    · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : Real.exp 1 * P ≤ 2.7182818286 * 2 := by gcongr
      linarith
  refine ⟨hcase, ?_⟩
  by_cases hS : 2 * d ≤ S
  · obtain ⟨h1, h2⟩ := hcase hS
    have : ((n : ℝ) * d) / 6 ≤ S := h2.trans h1
    have : (n : ℝ) * d ≤ 6 * S := by linarith
    exact_mod_cast this
  · push Not at hS
    obtain ⟨h1, h2⟩ := nc_sum_le_aux n d S hd hcount hn hS
    have : n * d ≤ 3 * d := Nat.mul_le_mul_right d (by omega)
    omega
