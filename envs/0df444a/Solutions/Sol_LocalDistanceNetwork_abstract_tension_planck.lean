-- Prove2me | solution 1 for LocalDistanceNetwork.abstract_tension_planck
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:34:35.882997+00:00
-- url     : https://prove2.me/submissions/23a57a1d-637f-4faf-835f-3c5e0c469fac

import Mathlib
import Definitions.Def_LocalDistanceNetwork_Tension
open LocalDistanceNetwork

theorem solution :
    (7.05 : ℝ) ≤ tensionSigma 73.50 0.81 67.24 0.35 ∧
    tensionSigma 73.50 0.81 67.24 0.35 < 7.15 := by
  unfold tensionSigma
  have a : |(73.50 : ℝ) - 67.24| = 6.26 := by norm_num [abs_of_pos]
  have s1 : 0.88 < Real.sqrt (0.81 ^ 2 + 0.35 ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt (0.81 ^ 2 + 0.35 ^ 2) < 0.885 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [a]
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith
