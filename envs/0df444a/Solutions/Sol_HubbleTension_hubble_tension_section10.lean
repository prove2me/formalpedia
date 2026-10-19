-- Prove2me | solution 1 for HubbleTension.hubble_tension_section10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:31:15.552736+00:00
-- url     : https://prove2.me/submissions/75eed636-c479-404d-b262-aa6902916e6a

import Mathlib
import Definitions.Def_HubbleTension_Defs
open HubbleTension

theorem solution :
    (4.5 ≤ tension 73.04 1.04 67.4 0.5 ∧ tension 73.04 1.04 67.4 0.5 < 5.5) ∧
    tension 72.0 1.5 67.4 0.5 < 3 ∧
    (1.5 ≤ tension 72.0 2.0 67.4 0.5 ∧ tension 72.0 2.0 67.4 0.5 < 2.5) := by
  unfold tension quadSum
  have a1 : |(73.04 : ℝ) - 67.4| = 5.64 := by norm_num [abs_of_pos]
  have a2 : |(72.0 : ℝ) - 67.4| = 4.6 := by norm_num [abs_of_pos]
  have s1 : 1.15 < Real.sqrt (1.04 ^ 2 + 0.5 ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt (1.04 ^ 2 + 0.5 ^ 2) < 1.16 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have s3 : 1.55 < Real.sqrt (1.5 ^ 2 + 0.5 ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s4 : 2 < Real.sqrt (2.0 ^ 2 + 0.5 ^ 2) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s5 : Real.sqrt (2.0 ^ 2 + 0.5 ^ 2) < 2.1 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [a1, a2]
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith
