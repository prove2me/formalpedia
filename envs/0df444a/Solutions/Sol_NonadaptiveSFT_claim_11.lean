-- Prove2me | solution 1 for NonadaptiveSFT.claim_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:24:06.666867+00:00
-- url     : https://prove2.me/submissions/c7065920-14bd-49ae-8959-7ea8691fa72e

import Mathlib

theorem solution (e : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ∑ i ∈ Finset.range (e + 1),
      ((2 : ℝ) ^ e / 2 ^ i) * min 1 ((2 ^ i * u / 2 ^ e) ^ 2) ≤ 4 * u := by
  rcases eq_or_lt_of_le hu with h0 | hpos
  · subst h0
    simp
  set φ : ℝ → ℝ := fun t => if t ≤ 1 then 2 * t else 4 - 2 / t with hφ
  have hφb : ∀ t, 0 < t → 0 ≤ φ t ∧ φ t ≤ 4 := by
    intro t ht
    simp only [hφ]
    split_ifs with h
    · constructor <;> linarith
    · push_neg at h
      have : 0 < 2 / t := by positivity
      have : 2 / t < 2 := by rw [div_lt_iff₀ ht]; linarith
      constructor <;> linarith
  have hstep : ∀ t, 0 < t → min t (1 / t) ≤ φ t - φ (t / 2) := by
    intro t ht
    simp only [hφ]
    by_cases h1 : t ≤ 1
    · rw [if_pos h1, if_pos (by linarith)]
      have := min_le_left t (1 / t)
      linarith
    · push_neg at h1
      rw [if_neg (by linarith)]
      have hm : min t (1 / t) = 1 / t := by
        apply min_eq_right
        rw [div_le_iff₀ ht]
        nlinarith
      rw [hm]
      by_cases h2 : t / 2 ≤ 1
      · rw [if_pos h2]
        rw [show 4 - 2 / t - 2 * (t / 2) = 4 - 2 / t - t by ring]
        have h3 : 1 / t + 2 / t = 3 / t := by ring
        have h4 : 3 / t ≤ 4 - t := by
          rw [div_le_iff₀ ht]
          nlinarith
        linarith
      · rw [if_neg h2]
        have e : 4 - 2 / t - (4 - 2 / (t / 2)) = 2 / t := by
          field_simp <;> ring
        rw [e]
        have : 0 < 1 / t := by positivity
        have : 2 / t = 2 * (1 / t) := by ring
        linarith
  set t : ℕ → ℝ := fun i => (2 : ℝ) ^ e / (2 ^ i * u) with ht
  have htpos : ∀ i, 0 < t i := fun i => by simp only [ht]; positivity
  have hthalf : ∀ i, t (i + 1) = t i / 2 := by
    intro i
    simp only [ht, pow_succ]
    field_simp
  have hterm : ∀ i ∈ Finset.range (e + 1),
      ((2 : ℝ) ^ e / 2 ^ i) * min 1 ((2 ^ i * u / 2 ^ e) ^ 2) = u * min (t i) (1 / t i) := by
    intro i _
    have hs : (0:ℝ) < 2 ^ e / 2 ^ i := by positivity
    rw [mul_min_of_nonneg _ _ hs.le, mul_min_of_nonneg _ _ hpos.le]
    congr 1
    · simp only [ht]
      field_simp
    · simp only [ht]
      field_simp <;> ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.range (e + 1), min (t i) (1 / t i) ≤ 4 := by
    calc ∑ i ∈ Finset.range (e + 1), min (t i) (1 / t i)
        ≤ ∑ i ∈ Finset.range (e + 1), (φ (t i) - φ (t (i + 1))) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hthalf]
          exact hstep _ (htpos i)
      _ = φ (t 0) - φ (t (e + 1)) := Finset.sum_range_sub' _ _
      _ ≤ 4 := by
          have := hφb (t 0) (htpos 0)
          have := hφb (t (e + 1)) (htpos (e + 1))
          linarith
  have := mul_le_mul_of_nonneg_left hsum hpos.le
  linarith
