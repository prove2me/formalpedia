-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window08
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:48:59.150657+00:00
-- url     : https://prove2.me/submissions/88e8d0ed-bcc7-46c5-8b80-d933261ff411

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s014_015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s016_017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s018_019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s020_021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s022_023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s024_025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s026_027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s028_029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w008_s030_031
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (65/4 : ℝ) ≤ p → p ≤ (261/16 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (4161/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (2081/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (4163/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (1041/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (4165/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (2083/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (4167/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s012_013 p (by linarith) h6
  by_cases h7 : p ≤ (521/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s014_015 p (by linarith) h7
  by_cases h8 : p ≤ (4169/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s016_017 p (by linarith) h8
  by_cases h9 : p ≤ (2085/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s018_019 p (by linarith) h9
  by_cases h10 : p ≤ (4171/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s020_021 p (by linarith) h10
  by_cases h11 : p ≤ (1043/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s022_023 p (by linarith) h11
  by_cases h12 : p ≤ (4173/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s024_025 p (by linarith) h12
  by_cases h13 : p ≤ (2087/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s026_027 p (by linarith) h13
  by_cases h14 : p ≤ (4175/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s028_029 p (by linarith) h14
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w008_s030_031 p (by linarith) hpb
#print axioms solution
