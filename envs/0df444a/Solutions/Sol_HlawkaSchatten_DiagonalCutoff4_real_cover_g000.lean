-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g000
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:51:50.120935+00:00
-- url     : https://prove2.me/submissions/0d0a7797-6cd3-41e4-a032-65a26bb9b4aa

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1018
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1020
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1024
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1026
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1028
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1030
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1031
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g000 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8193/2048 : ℝ)
  · exact real_three_w1000 p hpa h0
  by_cases h1 : p ≤ (4097/1024 : ℝ)
  · exact real_three_w1001 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8195/2048 : ℝ)
  · exact real_three_w1002 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2049/512 : ℝ)
  · exact real_three_w1003 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8197/2048 : ℝ)
  · exact real_three_w1004 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4099/1024 : ℝ)
  · exact real_three_w1005 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8199/2048 : ℝ)
  · exact real_three_w1006 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1025/256 : ℝ)
  · exact real_three_w1007 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8201/2048 : ℝ)
  · exact real_three_w1008 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4101/1024 : ℝ)
  · exact real_three_w1009 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8203/2048 : ℝ)
  · exact real_three_w1010 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2051/512 : ℝ)
  · exact real_three_w1011 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8205/2048 : ℝ)
  · exact real_three_w1012 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4103/1024 : ℝ)
  · exact real_three_w1013 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8207/2048 : ℝ)
  · exact real_three_w1014 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (513/128 : ℝ)
  · exact real_three_w1015 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8209/2048 : ℝ)
  · exact real_three_w1016 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4105/1024 : ℝ)
  · exact real_three_w1017 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8211/2048 : ℝ)
  · exact real_three_w1018 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2053/512 : ℝ)
  · exact real_three_w1019 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8213/2048 : ℝ)
  · exact real_three_w1020 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4107/1024 : ℝ)
  · exact real_three_w1021 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8215/2048 : ℝ)
  · exact real_three_w1022 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1027/256 : ℝ)
  · exact real_three_w1023 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8217/2048 : ℝ)
  · exact real_three_w1024 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4109/1024 : ℝ)
  · exact real_three_w1025 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8219/2048 : ℝ)
  · exact real_three_w1026 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2055/512 : ℝ)
  · exact real_three_w1027 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8221/2048 : ℝ)
  · exact real_three_w1028 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4111/1024 : ℝ)
  · exact real_three_w1029 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8223/2048 : ℝ)
  · exact real_three_w1030 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1031 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g000 p hpa hpb

#print axioms solution
