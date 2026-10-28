-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff12.cutoff12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T01:54:30.638103+00:00
-- url     : https://prove2.me/submissions/24f66888-644c-4ece-99dd-dee85abef444

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_real_three_w015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff16
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, 12 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  by_cases hp16 : 16 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff.cutoff16 p hp16
  apply HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three p (by linarith)
  by_cases h0 : p ≤ (49/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w000 p (by linarith) h0
  by_cases h1 : p ≤ (25/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w001 p (by linarith) h1
  by_cases h2 : p ≤ (51/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w002 p (by linarith) h2
  by_cases h3 : p ≤ (13 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w003 p (by linarith) h3
  by_cases h4 : p ≤ (53/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w004 p (by linarith) h4
  by_cases h5 : p ≤ (27/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w005 p (by linarith) h5
  by_cases h6 : p ≤ (55/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w006 p (by linarith) h6
  by_cases h7 : p ≤ (14 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w007 p (by linarith) h7
  by_cases h8 : p ≤ (57/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w008 p (by linarith) h8
  by_cases h9 : p ≤ (29/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w009 p (by linarith) h9
  by_cases h10 : p ≤ (59/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w010 p (by linarith) h10
  by_cases h11 : p ≤ (15 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w011 p (by linarith) h11
  by_cases h12 : p ≤ (61/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w012 p (by linarith) h12
  by_cases h13 : p ≤ (31/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w013 p (by linarith) h13
  by_cases h14 : p ≤ (63/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff12.real_three_w014 p (by linarith) h14
  exact HlawkaSchatten.DiagonalCutoff12.real_three_w015 p (by linarith) (by linarith)

#print axioms solution
