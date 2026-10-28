-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:01:11.634488+00:00
-- url     : https://prove2.me/submissions/c25a85fd-0e4f-4862-9b0a-0e4ec84a50ba

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s014_015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s016_017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s018_019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s020_021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s022_023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s024_025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s026_027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s028_029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w010_s030_031
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (131/8 : ℝ) ≤ p → p ≤ (263/16 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (4193/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (2097/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (4195/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (1049/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (4197/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (2099/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (4199/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s012_013 p (by linarith) h6
  by_cases h7 : p ≤ (525/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s014_015 p (by linarith) h7
  by_cases h8 : p ≤ (4201/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s016_017 p (by linarith) h8
  by_cases h9 : p ≤ (2101/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s018_019 p (by linarith) h9
  by_cases h10 : p ≤ (4203/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s020_021 p (by linarith) h10
  by_cases h11 : p ≤ (1051/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s022_023 p (by linarith) h11
  by_cases h12 : p ≤ (4205/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s024_025 p (by linarith) h12
  by_cases h13 : p ≤ (2103/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s026_027 p (by linarith) h13
  by_cases h14 : p ≤ (4207/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s028_029 p (by linarith) h14
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w010_s030_031 p (by linarith) hpb
#print axioms solution
