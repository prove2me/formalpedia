-- Prove2me | solution 1 for LL_Decomp587f.r3Nine_short
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T08:29:06.813175+00:00
-- url     : https://prove2.me/submissions/a058b49a-7607-495f-8498-3847893ae209

import Mathlib
import Definitions.Def_LL_Decomp587f_IsBuchstab
import Definitions.Def_LL_Decomp587f_ZeroBelowOne
import Definitions.Def_LL_Decomp587f_buchstabIntegral
import Theorems.Thm_LL_Decomp587f_r3Nine_sub0
import Theorems.Thm_LL_Decomp587f_r3Nine_sub1
import Theorems.Thm_LL_Decomp587f_r3Nine_sub2
import Theorems.Thm_LL_Decomp587f_r3Nine_sub3

open Real Set MeasureTheory LL_Decomp587f

theorem solution {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤
      (12408337 / 1000000000 : ℝ) := by
  by_cases h0 : φ ≤ (649 / 320 : ℝ)
  · exact r3Nine_sub0 hω hz hφ h0
  · by_cases h1 : φ ≤ (1307 / 640 : ℝ)
    · exact r3Nine_sub1 hω hz (le_of_not_ge h0) h1
    · by_cases h2 : φ ≤ (329 / 160 : ℝ)
      · exact r3Nine_sub2 hω hz (le_of_not_ge h1) h2
      · exact r3Nine_sub3 hω hz (le_of_not_ge h2) hφtop
