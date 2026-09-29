-- Prove2me | solution 1 for LassoDantzig.Lasso.lp_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:57:30.462992+00:00
-- url     : https://prove2.me/submissions/bc2bde8a-ca7b-40b6-9d33-2e9110ce5e5c

import Mathlib

private theorem lp_core {M : ℕ} (a : Fin M → ℝ) (ha : ∀ j, 0 ≤ a j) (p : ℝ)
    (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∑ j, a j ^ p ≤ (∑ j, a j) ^ (2 - p) * (∑ j, a j ^ 2) ^ (p - 1) := by
  have hA0 : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  have hB0 : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hpne : p ≠ 0 := ne_of_gt (by linarith)
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hzero : ∀ j, a j = 0 := by
      intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => ha k)).mp hA0'.symm j
        (Finset.mem_univ j)
    have hlhs : ∑ j, a j ^ p = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hzero j, Real.zero_rpow hpne]
    rw [hlhs]
    exact mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)
  · have hBpos : 0 < ∑ j, a j ^ 2 := by
      rcases eq_or_lt_of_le hB0 with hB0' | hBpos
      · exfalso
        have hz : ∀ j, a j ^ 2 = 0 := fun j =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k))).mp hB0'.symm j
            (Finset.mem_univ j)
        have hz0 : ∀ j, a j = 0 := fun j => pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hz j)
        have : ∑ j, a j = 0 := Finset.sum_eq_zero fun j _ => hz0 j
        linarith
      · exact hBpos
    have hden : 0 < (∑ j, a j) ^ (2 - p) * (∑ j, a j ^ 2) ^ (p - 1) :=
      mul_pos (Real.rpow_pos_of_pos hApos _) (Real.rpow_pos_of_pos hBpos _)
    have hkey : ∀ j : Fin M, a j ^ p
        ≤ ((∑ k, a k) ^ (2 - p) * (∑ k, a k ^ 2) ^ (p - 1)) *
          ((2 - p) * (a j / ∑ k, a k) + (p - 1) * (a j ^ 2 / ∑ k, a k ^ 2)) := by
      intro j
      have hgm := Real.geom_mean_le_arith_mean2_weighted
        (by linarith : (0 : ℝ) ≤ 2 - p) (by linarith : (0 : ℝ) ≤ p - 1)
        (div_nonneg (ha j) hA0) (div_nonneg (sq_nonneg (a j)) hB0)
        (by ring : (2 - p) + (p - 1) = 1)
      have hsum : (2 - p) + 2 * (p - 1) = p := by ring
      have e1 : a j ^ p = a j ^ (2 - p) * a j ^ (2 * (p - 1)) := by
        rw [← Real.rpow_add' (ha j) (by rw [hsum]; exact hpne), hsum]
      have e2 : (a j ^ 2) ^ (p - 1) = a j ^ (2 * (p - 1)) := by
        rw [← Real.rpow_natCast (a j) 2, ← Real.rpow_mul (ha j)]
        norm_num
      have hexp : (a j / ∑ k, a k) ^ (2 - p) * (a j ^ 2 / ∑ k, a k ^ 2) ^ (p - 1)
          = a j ^ p / ((∑ k, a k) ^ (2 - p) * (∑ k, a k ^ 2) ^ (p - 1)) := by
        rw [Real.div_rpow (ha j) hA0, Real.div_rpow (sq_nonneg (a j)) hB0,
          div_mul_div_comm, e2, e1]
      rw [hexp] at hgm
      have hD : a j ^ p
          = ((∑ k, a k) ^ (2 - p) * (∑ k, a k ^ 2) ^ (p - 1)) *
            (a j ^ p / ((∑ k, a k) ^ (2 - p) * (∑ k, a k ^ 2) ^ (p - 1))) := by
        field_simp
      rw [hD]
      exact mul_le_mul_of_nonneg_left hgm hden.le
    have hs1 : ∑ j, a j / (∑ k, a k) = 1 := by
      rw [← Finset.sum_div, div_self (ne_of_gt hApos)]
    have hs2 : ∑ j, a j ^ 2 / (∑ k, a k ^ 2) = 1 := by
      rw [← Finset.sum_div, div_self (ne_of_gt hBpos)]
    calc ∑ j, a j ^ p
        ≤ ∑ j, ((∑ k, a k) ^ (2 - p) * (∑ k, a k ^ 2) ^ (p - 1)) *
            ((2 - p) * (a j / ∑ k, a k) + (p - 1) * (a j ^ 2 / ∑ k, a k ^ 2)) :=
          Finset.sum_le_sum fun j _ => hkey j
      _ = ((∑ k, a k) ^ (2 - p) * (∑ k, a k ^ 2) ^ (p - 1)) *
            ∑ j, ((2 - p) * (a j / ∑ k, a k) + (p - 1) * (a j ^ 2 / ∑ k, a k ^ 2)) := by
          rw [Finset.mul_sum]
      _ = ((∑ k, a k) ^ (2 - p) * (∑ k, a k ^ 2) ^ (p - 1)) * 1 := by
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs1, hs2]
          ring
      _ = (∑ j, a j) ^ (2 - p) * (∑ j, a j ^ 2) ^ (p - 1) := mul_one _

private theorem lp_bound {M : ℕ} (a : Fin M → ℝ) (ha : ∀ j, 0 ≤ a j) (b1 b2 : ℝ)
    (h1 : ∑ j, a j ≤ b1) (h2 : ∑ j, a j ^ 2 ≤ b2) (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    (∑ j, a j) ^ (2 - p) * (∑ j, a j ^ 2) ^ (p - 1) ≤ b1 ^ (2 - p) * b2 ^ (p - 1) := by
  have hA0 : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  have hB0 : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hr1 : (∑ j, a j) ^ (2 - p) ≤ b1 ^ (2 - p) :=
    Real.rpow_le_rpow hA0 h1 (by linarith)
  have hr2 : (∑ j, a j ^ 2) ^ (p - 1) ≤ b2 ^ (p - 1) :=
    Real.rpow_le_rpow hB0 h2 (by linarith)
  exact mul_le_mul hr1 hr2 (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg (by linarith) _)

theorem solution {M : ℕ} (a : Fin M → ℝ) (ha : ∀ j, 0 ≤ a j) (b1 b2 : ℝ)
    (h1 : ∑ j, a j ≤ b1) (h2 : ∑ j, a j ^ 2 ≤ b2) (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∑ j, a j ^ p ≤ b1 ^ (2 - p) * b2 ^ (p - 1) :=
  le_trans (lp_core a ha p hp1 hp2) (lp_bound a ha b1 b2 h1 h2 p hp1 hp2)
