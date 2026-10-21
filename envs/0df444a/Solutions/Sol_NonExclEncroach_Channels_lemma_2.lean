-- Prove2me | solution 1 for NonExclEncroach.Channels.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:24:47.3223+00:00
-- url     : https://prove2.me/submissions/93c85c4f-cc55-4b44-a7c7-062163508121

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

open NonExclEncroach.Channels

/-- The unique maximizer over `[0,∞)` of a concave quadratic `K + m z - z²` is `max (m/2) 0`. -/
lemma quad_br (f : ℝ → ℝ) (K m : ℝ) (hf : ∀ z, f z = K + m * z - z ^ 2) :
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

theorem solution (θ c w1 w2 b q1 : ℝ) (hS : Standing θ c) (hw2 : 0 ≤ w2) (hb : 0 ≤ b)
    (hq1 : 0 ≤ q1) (hpos : q1 ≤ qbar1 θ c b → 0 ≤ q2IIIUpper θ c w2 b q1) :
    IsBestResponse (fun z => resellerProfit θ q1 z w1 w2 (yIII θ c b q1)) (q2III θ c w2 b q1) ∧
      ∀ z, IsBestResponse (fun z => resellerProfit θ q1 z w1 w2 (yIII θ c b q1)) z →
        z = q2III θ c w2 b q1 := by
  obtain ⟨h0, h1, -, -⟩ := hS
  set y := yIII θ c b q1 with hy
  have hq := quad_br (fun z => resellerProfit θ q1 z w1 w2 y)
    (q1 * (1 - q1 - y - w1)) (1 - 2 * θ * q1 - θ * y - w2)
    (fun z => by simp only [resellerProfit, p1, p2]; ring)
  have key : q2III θ c w2 b q1 = max ((1 - 2 * θ * q1 - θ * y - w2) / 2) 0 := by
    have hd : (4 - θ ^ 2) ≠ 0 := by nlinarith
    unfold q2III
    split_ifs with h
    · have hu := hpos h
      have : (1 - 2 * θ * q1 - θ * y - w2) / 2 = q2IIIUpper θ c w2 b q1 := by
        rw [hy]; unfold yIII q2IIIUpper; rw [if_pos h]; field_simp; ring
      rw [this, max_eq_left hu]
    · rw [hy]; unfold yIII; rw [if_neg h]; ring_nf
  rw [key]
  exact hq
