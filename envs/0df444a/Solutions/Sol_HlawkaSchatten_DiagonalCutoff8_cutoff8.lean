-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff8.cutoff8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T15:40:35.608314+00:00
-- url     : https://prove2.me/submissions/ab1a1086-453c-407c-8ca6-ab96b5b0e250

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w018
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w020
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w024
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w026
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w028
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w030
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_real_three_w031
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_cutoff12
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, 8 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  by_cases hp12 : 12 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff12.cutoff12 p hp12
  apply HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three p (by linarith)
  by_cases h0 : p ≤ (129/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w000 p (by linarith) h0
  by_cases h1 : p ≤ (65/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w001 p (by linarith) h1
  by_cases h2 : p ≤ (131/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w002 p (by linarith) h2
  by_cases h3 : p ≤ (33/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w003 p (by linarith) h3
  by_cases h4 : p ≤ (133/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w004 p (by linarith) h4
  by_cases h5 : p ≤ (67/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w005 p (by linarith) h5
  by_cases h6 : p ≤ (135/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w006 p (by linarith) h6
  by_cases h7 : p ≤ (17/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w007 p (by linarith) h7
  by_cases h8 : p ≤ (137/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w008 p (by linarith) h8
  by_cases h9 : p ≤ (69/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w009 p (by linarith) h9
  by_cases h10 : p ≤ (139/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w010 p (by linarith) h10
  by_cases h11 : p ≤ (35/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w011 p (by linarith) h11
  by_cases h12 : p ≤ (141/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w012 p (by linarith) h12
  by_cases h13 : p ≤ (71/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w013 p (by linarith) h13
  by_cases h14 : p ≤ (143/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w014 p (by linarith) h14
  by_cases h15 : p ≤ (9 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w015 p (by linarith) h15
  by_cases h16 : p ≤ (73/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w016 p (by linarith) h16
  by_cases h17 : p ≤ (37/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w017 p (by linarith) h17
  by_cases h18 : p ≤ (75/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w018 p (by linarith) h18
  by_cases h19 : p ≤ (19/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w019 p (by linarith) h19
  by_cases h20 : p ≤ (77/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w020 p (by linarith) h20
  by_cases h21 : p ≤ (39/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w021 p (by linarith) h21
  by_cases h22 : p ≤ (79/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w022 p (by linarith) h22
  by_cases h23 : p ≤ (10 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w023 p (by linarith) h23
  by_cases h24 : p ≤ (41/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w024 p (by linarith) h24
  by_cases h25 : p ≤ (21/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w025 p (by linarith) h25
  by_cases h26 : p ≤ (43/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w026 p (by linarith) h26
  by_cases h27 : p ≤ (11 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w027 p (by linarith) h27
  by_cases h28 : p ≤ (45/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w028 p (by linarith) h28
  by_cases h29 : p ≤ (23/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w029 p (by linarith) h29
  by_cases h30 : p ≤ (47/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff8.real_three_w030 p (by linarith) h30
  exact HlawkaSchatten.DiagonalCutoff8.real_three_w031 p (by linarith) (by linarith)

#print axioms solution
