-- Prove2me | solution 1 for JuschenkoMonod.a_apply_div_a_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:41:29.000295+00:00
-- url     : https://prove2.me/submissions/ee70333a-f3bd-416b-afc7-f0bfe500a9dc

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

lemma exp_sub_one_sub_le (y : ℝ) : |Real.exp y - 1 - y| ≤ 3 * y ^ 2 * Real.exp |y| := by
  have he : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg y)
  have hey : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.mpr (le_abs_self y)
  by_cases h1 : |y| ≤ 1
  · have := Real.abs_exp_sub_one_sub_id_le h1
    have h2 : y ^ 2 ≤ 3 * y ^ 2 * Real.exp |y| := by nlinarith [sq_nonneg y]
    linarith
  · push_neg at h1
    have hy2 : 1 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have hay : |y| ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have h3 : |Real.exp y - 1 - y| ≤ Real.exp y + 1 + |y| := by
      have := abs_sub (Real.exp y - 1) y
      have h4 := abs_sub (Real.exp y) 1
      rw [abs_of_pos (Real.exp_pos y)] at h4
      simp at h4
      linarith
    nlinarith [Real.exp_pos y, mul_le_mul_of_nonneg_right hy2.le (Real.exp_pos |y|).le]

theorem a_aux (c : ℝ) :
    ∃ C C' C'' : ℝ, ∀ g ∈ IntervalExchange.wobbling ℤ, wobblingNorm g = c →
      ∀ n : ℕ, 0 < n → ∀ j : ℤ, ∃ η ϑ : ℝ,
        a n (g j) / a n j = Real.exp (Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j| + η)) ∧
        |η| ≤ C / n ∧
        a n (g j) / a n j - 1 =
          Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j|) + η * Real.exp (-(|j| : ℝ) / n) + ϑ ∧
        |ϑ| ≤ C' * Real.exp (-2 * (|j| : ℝ) / n) ∧
        |a n (g j) / a n j - 1| ≤ C'' * Real.exp (-(|j| : ℝ) / n) := by
  set C := 3 * c ^ 2 * Real.exp c with hC
  set K := c + C with hK
  refine ⟨C, 3 * K ^ 2 * Real.exp K, K * (1 + 3 * K * Real.exp K), ?_⟩
  rintro g ⟨B, hB⟩ hgc n hn j
  have hbdd : BddAbove (Set.range fun j : ℤ => (|g j - j| : ℝ)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := hB j
    rw [Int.dist_eq] at this
    simpa using this
  have hw : ∀ j, (|g j - j| : ℝ) ≤ c := fun j => hgc ▸ le_ciSup hbdd j
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hw 0)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  set E := Real.exp (-(|j| : ℝ) / n) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    have : 0 ≤ (|j| : ℝ) / n := by positivity
    rw [neg_div]; linarith
  set d : ℝ := |(g j : ℝ)| - |(j : ℝ)| with hd
  have hdc : |d| ≤ c := by
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    have := hw j
    push_cast at this
    exact this
  set η : ℝ := n * (1 - Real.exp (-d / n)) - d with hη
  have hηb : |η| ≤ C / n := by
    have h1 : η = -(n * (Real.exp (-d / n) - 1 - (-d / n))) := by
      rw [hη]; field_simp; ring
    rw [h1, abs_neg, abs_mul, abs_of_pos hn0]
    have h2 := exp_sub_one_sub_le (-d / n)
    have h3 : |(-d / n)| ≤ c := by
      rw [abs_div, abs_neg, abs_of_pos hn0]
      calc |d| / n ≤ |d| := div_le_self (abs_nonneg _) hn1
        _ ≤ c := hdc
    have h4 : (3 * (-d / n) ^ 2 * Real.exp |(-d / n)|) ≤ 3 * (d ^ 2 / n ^ 2) * Real.exp c := by
      have : (-d / n) ^ 2 = d ^ 2 / n ^ 2 := by ring
      rw [this]
      gcongr
    have h5 : d ^ 2 ≤ c ^ 2 := by
      have := sq_le_sq' (abs_le.mp hdc).1 (abs_le.mp hdc).2
      exact this
    calc (n:ℝ) * |Real.exp (-d / n) - 1 - (-d / n)| ≤ n * (3 * (d ^ 2 / n ^ 2) * Real.exp c) :=
          by gcongr; exact h2.trans h4
      _ = 3 * d ^ 2 * Real.exp c / n := by field_simp
      _ ≤ 3 * c ^ 2 * Real.exp c / n := by gcongr
  set t := E * (d + η) with ht
  have hrat : a n (g j) / a n j = Real.exp t := by
    unfold a
    rw [← Real.exp_sub]
    congr 1
    have h1 : Real.exp (-(|(g j : ℝ)| : ℝ) / n) = E * Real.exp (-d / n) := by
      rw [hE, ← Real.exp_add]; congr 1; rw [hd]; ring
    rw [h1, ht, hη, ← hE]
    ring
  have hC0 : 0 ≤ C := by positivity
  have hK0 : 0 ≤ K := by linarith
  have htK : |t| ≤ K := by
    rw [ht, abs_mul, abs_of_pos hE0]
    have h1 : |d + η| ≤ K := by
      calc |d + η| ≤ |d| + |η| := abs_add_le _ _
        _ ≤ c + C := by
          gcongr
          exact hηb.trans (div_le_self hC0 hn1)
    calc E * |d + η| ≤ 1 * K := by gcongr
      _ = K := one_mul K
  have hE2 : Real.exp (-2 * (|j| : ℝ) / n) = E ^ 2 := by
    rw [hE, sq, ← Real.exp_add]; congr 1; ring
  have hϑ : |Real.exp t - 1 - t| ≤ 3 * K ^ 2 * Real.exp K * E ^ 2 := by
    refine (exp_sub_one_sub_le t).trans ?_
    have ht2 : t ^ 2 ≤ K ^ 2 * E ^ 2 := by
      have : t ^ 2 = E ^ 2 * (d + η) ^ 2 := by rw [ht]; ring
      rw [this]
      have : (d + η) ^ 2 ≤ K ^ 2 := by
        have := abs_le.mp (show |d + η| ≤ K from by
          calc |d + η| ≤ |d| + |η| := abs_add_le _ _
            _ ≤ c + C := by
              gcongr
              exact hηb.trans (div_le_self hC0 hn1))
        nlinarith [this.1, this.2]
      nlinarith [sq_nonneg E]
    have : Real.exp |t| ≤ Real.exp K := Real.exp_le_exp.mpr htK
    calc 3 * t ^ 2 * Real.exp |t| ≤ 3 * (K ^ 2 * E ^ 2) * Real.exp K := by gcongr
      _ = _ := by ring
  have hcast : ((|j| : ℤ) : ℝ) = |(j:ℝ)| := Int.cast_abs
  refine ⟨η, Real.exp t - 1 - t, ?_, hηb, ?_, ?_, ?_⟩
  · rw [hrat, ht, hcast]
  · rw [hrat, ht, hcast]; ring
  · rw [hE2]; linarith [hϑ]
  · rw [hrat]
    have h1 : |Real.exp t - 1| ≤ |t| + |Real.exp t - 1 - t| := by
      have := abs_add_le t (Real.exp t - 1 - t)
      simpa using this
    have h2 : |t| ≤ K * E := by
      rw [ht, abs_mul, abs_of_pos hE0]
      have : |d + η| ≤ K := by
        calc |d + η| ≤ |d| + |η| := abs_add_le _ _
          _ ≤ c + C := by
            gcongr
            exact hηb.trans (div_le_self hC0 hn1)
      nlinarith
    have h3 : 3 * K ^ 2 * Real.exp K * E ^ 2 ≤ 3 * K ^ 2 * Real.exp K * E := by
      have h0 : 0 ≤ 3 * K ^ 2 * Real.exp K := by positivity
      exact mul_le_mul_of_nonneg_left (by nlinarith) h0
    calc |Real.exp t - 1| ≤ |t| + |Real.exp t - 1 - t| := h1
      _ ≤ K * E + 3 * K ^ 2 * Real.exp K * E := add_le_add h2 (hϑ.trans h3)
      _ = K * (1 + 3 * K * Real.exp K) * E := by ring

end JuschenkoMonod

theorem solution : ∀ (c : ℝ),
    ∃ C C' C'' : ℝ, ∀ g ∈ IntervalExchange.wobbling ℤ, JuschenkoMonod.wobblingNorm g = c →
      ∀ n : ℕ, 0 < n → ∀ j : ℤ, ∃ η ϑ : ℝ,
        JuschenkoMonod.a n (g j) / JuschenkoMonod.a n j = Real.exp (Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j| + η)) ∧
        |η| ≤ C / n ∧
        JuschenkoMonod.a n (g j) / JuschenkoMonod.a n j - 1 =
          Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j|) + η * Real.exp (-(|j| : ℝ) / n) + ϑ ∧
        |ϑ| ≤ C' * Real.exp (-2 * (|j| : ℝ) / n) ∧
        |JuschenkoMonod.a n (g j) / JuschenkoMonod.a n j - 1| ≤ C'' * Real.exp (-(|j| : ℝ) / n) :=
  JuschenkoMonod.a_aux
