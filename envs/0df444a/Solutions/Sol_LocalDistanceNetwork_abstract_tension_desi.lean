-- Prove2me | solution 1 for LocalDistanceNetwork.abstract_tension_desi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:34:43.364711+00:00
-- url     : https://prove2.me/submissions/ff8fd58a-c8c5-46d3-af9c-be94d43345d4

import Mathlib
import Definitions.Def_LocalDistanceNetwork_Tension
open LocalDistanceNetwork

theorem solution :
    (4.95 : ℝ) ≤ tensionSigma 73.50 0.81 68.51 0.58 ∧
    tensionSigma 73.50 0.81 68.51 0.58 < 5.05 := by
  unfold tensionSigma
  have a : |(73.50 : ℝ) - 68.51| = 4.99 := by norm_num [abs_of_pos]
  have s1 : 0.99 < Real.sqrt (0.81 ^ 2 + 0.58 ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt (0.81 ^ 2 + 0.58 ^ 2) < 1 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [a]
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith
