-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window02
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:35:11.482967+00:00
-- url     : https://prove2.me/submissions/884355a2-9795-4c00-9e5d-d68790b53864

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w002_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (257/16 : ℝ) ≤ p → p ≤ (515/32 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (4113/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (2057/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (4115/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (1029/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (4117/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (2059/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (4119/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w002_s014_015 p (by linarith) hpb
#print axioms solution
