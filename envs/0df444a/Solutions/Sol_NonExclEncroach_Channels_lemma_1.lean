-- Prove2me | solution 1 for NonExclEncroach.Channels.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:26:26.430983+00:00
-- url     : https://prove2.me/submissions/783f600c-1134-4b2d-9413-be8c48911c17

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

open NonExclEncroach.Channels

/-- The unique maximizer over `[0,∞)` of a concave quadratic `K + m z - z²` is `max (m/2) 0`. -/
lemma quad_br1 (f : ℝ → ℝ) (K m : ℝ) (hf : ∀ z, f z = K + m * z - z ^ 2) :
    IsBestResponse f (max (m / 2) 0) ∧ ∀ x, IsBestResponse f x → x = max (m / 2) 0 := by
  have hbr : IsBestResponse f (max (m / 2) 0) := by
    refine ⟨le_max_right _ _, fun z hz => ?_⟩
    rw [hf, hf]
    rcases le_total 0 m with h | h
    · rw [max_eq_left (by linarith)]
      nlinarith [sq_nonneg (z - m / 2)]
    · rw [max_eq_right (by linarith)]
      nlinarith
  refine ⟨hbr, fun x hx => ?_⟩
  have e1 := hx.2 _ hbr.1
  have e2 := hbr.2 x hx.1
  rw [hf, hf] at e1 e2
  rcases le_total 0 m with h | h
  · rw [max_eq_left (by linarith)] at e1 e2 ⊢
    nlinarith [sq_nonneg (x - m / 2)]
  · rw [max_eq_right (by linarith)] at e1 e2 ⊢
    nlinarith [hx.1]

/-- Stage III is equivalent to the two positive-part best-response equations. -/
lemma stageIII_iff (θ c b q1 y q2' : ℝ) :
    IsStageIII θ c b q1 y q2' ↔
      y = max ((1 - q1 - θ * q2' - c) / 2) 0 ∧
      q2' = max ((1 - 2 * θ * q1 - θ * y - b) / 2) 0 := by
  have hA := quad_br1 (fun z => z * (pd θ q1 q2' z - c)) 0 (1 - q1 - θ * q2' - c)
    (fun z => by simp only [pd]; ring)
  have hB := quad_br1 (fun z => resellerProfit θ q1 z 0 b y) (q1 * (1 - q1 - y))
    (1 - 2 * θ * q1 - θ * y - b) (fun z => by simp only [resellerProfit, p1, p2]; ring)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hA.2 y h1, hB.2 q2' h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1]; exact hA.1
    · rw [h2]; exact hB.1

lemma abs_max_sub_max (a a' : ℝ) : |max a 0 - max a' 0| ≤ |a - a'| :=
  abs_max_sub_max_le_abs a a' 0

theorem solution (θ c b q1 : ℝ) (hS : Standing θ c) (hb : 0 ≤ b) (hq1 : 0 ≤ q1)
    (hR : ∀ x, 0 ≤ x → x ≤ qbar1 θ c b → 0 < q2conjUpper θ c b x) :
    IsStageIII θ c b q1 (yIII θ c b q1) (q2conj θ c b q1) ∧
      ∀ y q2', IsStageIII θ c b q1 y q2' → y = yIII θ c b q1 ∧ q2' = q2conj θ c b q1 := by
  obtain ⟨h0, h1, -, -⟩ := hS
  have hd : (4 - θ ^ 2) ≠ 0 := by nlinarith
  have hd' : 0 < 4 - θ ^ 2 := by nlinarith
  have hk : 0 < 1 - θ ^ 2 := by nlinarith
  have hex : IsStageIII θ c b q1 (yIII θ c b q1) (q2conj θ c b q1) := by
    rw [stageIII_iff]
    by_cases h : q1 ≤ qbar1 θ c b
    · have hq := hR q1 hq1 h
      have hyu : 0 ≤ (2 * (1 - c) - θ * (1 - b)) / (4 - θ ^ 2)
          - 2 * (1 - θ ^ 2) / (4 - θ ^ 2) * q1 := by
        unfold qbar1 at h
        rw [le_div_iff₀ (by positivity)] at h
        have e : (2 * (1 - c) - θ * (1 - b)) / (4 - θ ^ 2)
            - 2 * (1 - θ ^ 2) / (4 - θ ^ 2) * q1
            = (2 * (1 - c) - θ * (1 - b) - 2 * (1 - θ ^ 2) * q1) / (4 - θ ^ 2) := by
          field_simp
        rw [e]
        apply div_nonneg _ hd'.le; linarith
      unfold yIII q2conj
      rw [if_pos h, if_pos h]
      constructor
      · have : (1 - q1 - θ * q2conjUpper θ c b q1 - c) / 2 =
            (2 * (1 - c) - θ * (1 - b)) / (4 - θ ^ 2) - 2 * (1 - θ ^ 2) / (4 - θ ^ 2) * q1 := by
          unfold q2conjUpper; field_simp; ring
        rw [this, max_eq_left hyu]
      · have : (1 - 2 * θ * q1 - θ * ((2 * (1 - c) - θ * (1 - b)) / (4 - θ ^ 2)
            - 2 * (1 - θ ^ 2) / (4 - θ ^ 2) * q1) - b) / 2 = q2conjUpper θ c b q1 := by
          unfold q2conjUpper; field_simp; ring
        rw [this, max_eq_left hq.le]
    · push Not at h
      have h' : 2 * (1 - c) - θ * (1 - b) < 2 * (1 - θ ^ 2) * q1 := by
        unfold qbar1 at h; rw [div_lt_iff₀ (by positivity)] at h; linarith
      unfold yIII q2conj
      rw [if_neg (not_le.mpr h), if_neg (not_le.mpr h)]
      refine ⟨?_, by ring_nf⟩
      symm; apply max_eq_right
      rcases le_total 0 ((1 - 2 * θ * q1 - b) / 2) with hm | hm
      · rw [max_eq_left hm]; nlinarith
      · rw [max_eq_right hm]; nlinarith
  refine ⟨hex, fun y q2' hst => ?_⟩
  rw [stageIII_iff] at hst hex
  obtain ⟨ey, eq⟩ := hst
  obtain ⟨fy, fq⟩ := hex
  set Y := yIII θ c b q1
  set Q := q2conj θ c b q1
  have i1 : |y - Y| ≤ θ / 2 * |q2' - Q| := by
    rw [ey, fy]
    refine (abs_max_sub_max _ _).trans (le_of_eq ?_)
    rw [show (1 - q1 - θ * q2' - c) / 2 - (1 - q1 - θ * Q - c) / 2 = -(θ / 2) * (q2' - Q) by ring,
      abs_mul, abs_neg, abs_of_pos (by linarith)]
  have i2 : |q2' - Q| ≤ θ / 2 * |y - Y| := by
    rw [eq, fq]
    refine (abs_max_sub_max _ _).trans (le_of_eq ?_)
    rw [show (1 - 2 * θ * q1 - θ * y - b) / 2 - (1 - 2 * θ * q1 - θ * Y - b) / 2
        = -(θ / 2) * (y - Y) by ring, abs_mul, abs_neg, abs_of_pos (by linarith)]
  have a1 := abs_nonneg (y - Y)
  have a2 := abs_nonneg (q2' - Q)
  have z1 : |y - Y| = 0 := by nlinarith
  have z2 : |q2' - Q| = 0 := by nlinarith
  exact ⟨by linarith [abs_eq_zero.mp z1], by linarith [abs_eq_zero.mp z2]⟩
