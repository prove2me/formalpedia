-- Prove2me | solution 1 for NonExclEncroach.Channels.lemma_4_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:22:35.230854+00:00
-- url     : https://prove2.me/submissions/c37ebc9d-e3de-4d73-972f-7f462eda6523

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

open NonExclEncroach.Channels

theorem solution (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    c0 θ ≤ c1 θ ∧ c1 θ ≤ c2 θ ∧ c2 θ ≤ c3 θ := by
  have a2 : θ ^ 2 < 1 := by nlinarith
  have a4 : θ ^ 4 < 1 := by nlinarith
  have a6 : θ ^ 6 < 1 := by nlinarith
  have p2 : 0 < θ ^ 2 := by positivity
  have p4 : 0 < θ ^ 4 := by positivity
  have p6 : 0 < θ ^ 6 := by positivity
  have p8 : 0 < θ ^ 8 := by positivity
  have D0 : 0 < 2 * (8 - 5 * θ ^ 2) := by linarith
  have D1 : 0 < 32 - 26 * θ ^ 2 := by linarith
  have D2' : 0 < 128 - 16 * θ ^ 2 - 13 * θ ^ 4 := by linarith
  have D2 : 0 < 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by positivity
  have D3 : 0 < 2 * (320 - 36 * θ ^ 2 - 42 * θ ^ 4 + θ ^ 6) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold c0 c1
    rw [neg_div, ← neg_div, div_le_div_iff₀ D0 D1]
    have key : (4 * θ - 14 * θ ^ 2 + 5 * θ ^ 3 - θ ^ 4) * (2 * (8 - 5 * θ ^ 2))
        - (-((2 - θ) * (8 - θ ^ 2 - θ ^ 3))) * (32 - 26 * θ ^ 2)
        = 8 * (1 - θ) * (1 + θ) * (8 - θ ^ 2) * (8 - 3 * θ - 2 * θ ^ 2) := by ring
    have : 0 ≤ 8 * (1 - θ) * (1 + θ) * (8 - θ ^ 2) * (8 - 3 * θ - 2 * θ ^ 2) := by
      have e1 : 0 ≤ 1 - θ := by linarith
      have e2 : 0 ≤ 1 + θ := by linarith
      have e3 : 0 ≤ 8 - θ ^ 2 := by linarith
      have e4 : 0 ≤ 8 - 3 * θ - 2 * θ ^ 2 := by linarith
      positivity
    linarith
  · unfold c1 c2
    rw [div_le_div_iff₀ D1 D2]
    have key : (32 * θ - 80 * θ ^ 2 - 32 * θ ^ 3 - 14 * θ ^ 4 - 8 * θ ^ 5 + 4 * θ ^ 6 - θ ^ 7)
          * (32 - 26 * θ ^ 2)
        - (4 * θ - 14 * θ ^ 2 + 5 * θ ^ 3 - θ ^ 4) *
          (2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4))
        = 18 * θ ^ 3 * (5 * θ ^ 2 + 4) * (8 + 4 * θ - θ ^ 2) := by ring
    have : 0 ≤ 18 * θ ^ 3 * (5 * θ ^ 2 + 4) * (8 + 4 * θ - θ ^ 2) := by
      have e : 0 ≤ 8 + 4 * θ - θ ^ 2 := by linarith
      positivity
    linarith
  · unfold c2 c3
    rw [div_le_div_iff₀ D2 D3]
    have key : (384 - 64 * θ + 8 * θ ^ 2 - 24 * θ ^ 3 - 60 * θ ^ 4 + 6 * θ ^ 5 - 9 * θ ^ 6
            + θ ^ 7 + θ ^ 8) * (2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4))
        - (32 * θ - 80 * θ ^ 2 - 32 * θ ^ 3 - 14 * θ ^ 4 - 8 * θ ^ 5 + 4 * θ ^ 6 - θ ^ 7)
          * (2 * (320 - 36 * θ ^ 2 - 42 * θ ^ 4 + θ ^ 6))
        = 6 * (2 - θ) * (θ + 2) ^ 2 * (2 * θ ^ 2 + θ + 8)
          * (2 * θ ^ 8 - 11 * θ ^ 6 - 52 * θ ^ 4 + 48 * θ ^ 2 + 256) := by ring
    have : 0 ≤ 6 * (2 - θ) * (θ + 2) ^ 2 * (2 * θ ^ 2 + θ + 8)
          * (2 * θ ^ 8 - 11 * θ ^ 6 - 52 * θ ^ 4 + 48 * θ ^ 2 + 256) := by
      have e1 : 0 ≤ 2 - θ := by linarith
      have e2 : 0 ≤ 2 * θ ^ 8 - 11 * θ ^ 6 - 52 * θ ^ 4 + 48 * θ ^ 2 + 256 := by linarith
      positivity
    linarith
