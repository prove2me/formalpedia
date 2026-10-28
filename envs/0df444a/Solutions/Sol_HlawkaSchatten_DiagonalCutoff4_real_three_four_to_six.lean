-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_three_four_to_six
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:50.836999+00:00
-- url     : https://prove2.me/submissions/c5fa8071-4df3-4d1c-9edc-be4814591c06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g018
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g020
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_cover_g024
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4
theorem solution :
    ∀ p : ℝ, 4 ≤ p → p ≤ 6 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hpa hpb
  by_cases h0 : p ≤ (257/64 : ℝ)
  · exact real_cover_g000 p hpa h0
  by_cases h1 : p ≤ (129/32 : ℝ)
  · exact real_cover_g001 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (259/64 : ℝ)
  · exact real_cover_g002 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (65/16 : ℝ)
  · exact real_cover_g003 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (261/64 : ℝ)
  · exact real_cover_g004 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (131/32 : ℝ)
  · exact real_cover_g005 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (263/64 : ℝ)
  · exact real_cover_g006 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (33/8 : ℝ)
  · exact real_cover_g007 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (4247/1024 : ℝ)
  · exact real_cover_g008 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4279/1024 : ℝ)
  · exact real_cover_g009 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (4311/1024 : ℝ)
  · exact real_cover_g010 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4343/1024 : ℝ)
  · exact real_cover_g011 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (4375/1024 : ℝ)
  · exact real_cover_g012 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4407/1024 : ℝ)
  · exact real_cover_g013 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (4455/1024 : ℝ)
  · exact real_cover_g014 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4519/1024 : ℝ)
  · exact real_cover_g015 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4583/1024 : ℝ)
  · exact real_cover_g016 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4647/1024 : ℝ)
  · exact real_cover_g017 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4747/1024 : ℝ)
  · exact real_cover_g018 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4875/1024 : ℝ)
  · exact real_cover_g019 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (5003/1024 : ℝ)
  · exact real_cover_g020 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (5247/1024 : ℝ)
  · exact real_cover_g021 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (5535/1024 : ℝ)
  · exact real_cover_g022 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (6047/1024 : ℝ)
  · exact real_cover_g023 p (le_of_lt (lt_of_not_ge h22)) h23
  exact real_cover_g024 p (le_of_lt (lt_of_not_ge h23)) hpb

#print axioms solution
