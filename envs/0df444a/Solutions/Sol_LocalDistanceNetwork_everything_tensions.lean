-- Prove2me | solution 1 for LocalDistanceNetwork.everything_tensions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:34:52.939701+00:00
-- url     : https://prove2.me/submissions/004549a2-045f-4440-ba21-bd23a8f54748

import Mathlib
import Definitions.Def_LocalDistanceNetwork_Tension
open LocalDistanceNetwork

theorem solution :
    ((8.65 : ℝ) ≤ tensionSigma 73.994 0.697 67.24 0.35 ∧
      tensionSigma 73.994 0.697 67.24 0.35 < 8.75) ∧
    ((8.05 : ℝ) ≤ tensionSigma 73.656 0.713 67.24 0.35 ∧
      tensionSigma 73.656 0.713 67.24 0.35 < 8.15) := by
  unfold tensionSigma
  have a1 : |(73.994 : ℝ) - 67.24| = 6.754 := by norm_num [abs_of_pos]
  have a2 : |(73.656 : ℝ) - 67.24| = 6.416 := by norm_num [abs_of_pos]
  have s1 : 0.775 < Real.sqrt (0.697 ^ 2 + 0.35 ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt (0.697 ^ 2 + 0.35 ^ 2) < 0.7808 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s3 : 0.79 < Real.sqrt (0.713 ^ 2 + 0.35 ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s4 : Real.sqrt (0.713 ^ 2 + 0.35 ^ 2) < 0.797 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [a1, a2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith
