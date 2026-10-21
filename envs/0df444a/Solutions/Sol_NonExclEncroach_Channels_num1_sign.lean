-- Prove2me | solution 1 for NonExclEncroach.Channels.num1_sign
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:18:47.897678+00:00
-- url     : https://prove2.me/submissions/92ee809f-79b5-46d1-abe1-cb34c885589a

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

open NonExclEncroach.Channels

theorem solution :
    StrictAntiOn num1 (Set.Icc 0 1) ∧ 0 < num1 (1 / 10) ∧ num1 1 < 0 ∧
      ∀ θ, 0 < θ → θ < 1 → (0 < c2 θ ↔ 0 < num1 θ) ∧ (c2 θ < 0 ↔ num1 θ < 0) := by
  refine ⟨?_, by norm_num [num1], by norm_num [num1], ?_⟩
  · intro x hx y hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    have key : num1 x - num1 y = (y - x) *
        (80 + 32 * (x + y) + 14 * (x ^ 2 + x * y + y ^ 2)
          + 8 * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)
          - 4 * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4)
          + (x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5)) := by
      unfold num1; ring
    have h4 : x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 ≤ 5 := by
      have a1 : x ^ 4 ≤ 1 := pow_le_one₀ hx0 hx1
      have a2 : x ^ 3 * y ≤ 1 := mul_le_one₀ (pow_le_one₀ hx0 hx1) hy0 hy1
      have a3 : x ^ 2 * y ^ 2 ≤ 1 :=
        mul_le_one₀ (pow_le_one₀ hx0 hx1) (pow_nonneg hy0 _) (pow_le_one₀ hy0 hy1)
      have a4 : x * y ^ 3 ≤ 1 := mul_le_one₀ hx1 (pow_nonneg hy0 _) (pow_le_one₀ hy0 hy1)
      have a5 : y ^ 4 ≤ 1 := pow_le_one₀ hy0 hy1
      linarith
    have hpos : 0 < 80 + 32 * (x + y) + 14 * (x ^ 2 + x * y + y ^ 2)
          + 8 * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)
          - 4 * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4)
          + (x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5) := by
      have : 0 ≤ x + y := by positivity
      have : 0 ≤ x ^ 2 + x * y + y ^ 2 := by positivity
      have : 0 ≤ x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 := by positivity
      have : 0 ≤ x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5 := by
        positivity
      linarith
    have : 0 < num1 x - num1 y := by
      rw [key]; exact mul_pos (by linarith) hpos
    linarith
  · intro θ h0 h1
    have hden : 0 < 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by
      have a : θ ^ 2 < 1 := by nlinarith
      have b : θ ^ 4 < 1 := by nlinarith
      have : 0 < 128 - 16 * θ ^ 2 - 13 * θ ^ 4 := by linarith
      positivity
    have hc2 : c2 θ = θ * num1 θ / (2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4)) := by
      unfold c2 num1; ring_nf
    rw [hc2]
    constructor
    · rw [div_pos_iff_of_pos_right hden]
      exact ⟨fun h => pos_of_mul_pos_right h h0.le, fun h => mul_pos h0 h⟩
    · rw [div_neg_iff]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact absurd h (not_lt.mpr hden.le)
        · by_contra hn
          push_neg at hn
          exact absurd h (not_lt.mpr (mul_nonneg h0.le hn))
      · intro h
        exact Or.inr ⟨mul_neg_of_pos_of_neg h0 h, hden⟩
