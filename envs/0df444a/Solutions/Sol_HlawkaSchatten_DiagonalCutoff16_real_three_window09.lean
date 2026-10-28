-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window09
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:58:32.584002+00:00
-- url     : https://prove2.me/submissions/eefd06de-001c-4a94-b041-3a35a852fe41

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s014_015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s016_017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s018_019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s020_021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s022_023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s024_025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s026_027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s028_029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w009_s030_031
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (261/16 : ℝ) ≤ p → p ≤ (131/8 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (4177/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (2089/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (4179/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (1045/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (4181/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (2091/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (4183/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s012_013 p (by linarith) h6
  by_cases h7 : p ≤ (523/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s014_015 p (by linarith) h7
  by_cases h8 : p ≤ (4185/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s016_017 p (by linarith) h8
  by_cases h9 : p ≤ (2093/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s018_019 p (by linarith) h9
  by_cases h10 : p ≤ (4187/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s020_021 p (by linarith) h10
  by_cases h11 : p ≤ (1047/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s022_023 p (by linarith) h11
  by_cases h12 : p ≤ (4189/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s024_025 p (by linarith) h12
  by_cases h13 : p ≤ (2095/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s026_027 p (by linarith) h13
  by_cases h14 : p ≤ (4191/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s028_029 p (by linarith) h14
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w009_s030_031 p (by linarith) hpb
#print axioms solution
