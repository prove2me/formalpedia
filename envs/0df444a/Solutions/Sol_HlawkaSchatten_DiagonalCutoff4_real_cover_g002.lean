-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g002
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:33.87299+00:00
-- url     : https://prove2.me/submissions/849f615f-4aa5-4397-b185-4bb1a0fcde82

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1064
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1065
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1066
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1067
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1068
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1069
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1070
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1071
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1072
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1073
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1074
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1075
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1076
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1077
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1078
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1079
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1080
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1081
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1082
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1083
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1084
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1085
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1086
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1087
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1088
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1089
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1090
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1091
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1092
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1093
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1094
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1095
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g002 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8257/2048 : ℝ)
  · exact real_three_w1064 p hpa h0
  by_cases h1 : p ≤ (4129/1024 : ℝ)
  · exact real_three_w1065 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8259/2048 : ℝ)
  · exact real_three_w1066 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2065/512 : ℝ)
  · exact real_three_w1067 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8261/2048 : ℝ)
  · exact real_three_w1068 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4131/1024 : ℝ)
  · exact real_three_w1069 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8263/2048 : ℝ)
  · exact real_three_w1070 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1033/256 : ℝ)
  · exact real_three_w1071 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8265/2048 : ℝ)
  · exact real_three_w1072 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4133/1024 : ℝ)
  · exact real_three_w1073 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8267/2048 : ℝ)
  · exact real_three_w1074 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2067/512 : ℝ)
  · exact real_three_w1075 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8269/2048 : ℝ)
  · exact real_three_w1076 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4135/1024 : ℝ)
  · exact real_three_w1077 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8271/2048 : ℝ)
  · exact real_three_w1078 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (517/128 : ℝ)
  · exact real_three_w1079 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8273/2048 : ℝ)
  · exact real_three_w1080 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4137/1024 : ℝ)
  · exact real_three_w1081 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8275/2048 : ℝ)
  · exact real_three_w1082 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2069/512 : ℝ)
  · exact real_three_w1083 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8277/2048 : ℝ)
  · exact real_three_w1084 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4139/1024 : ℝ)
  · exact real_three_w1085 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8279/2048 : ℝ)
  · exact real_three_w1086 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1035/256 : ℝ)
  · exact real_three_w1087 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8281/2048 : ℝ)
  · exact real_three_w1088 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4141/1024 : ℝ)
  · exact real_three_w1089 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8283/2048 : ℝ)
  · exact real_three_w1090 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2071/512 : ℝ)
  · exact real_three_w1091 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8285/2048 : ℝ)
  · exact real_three_w1092 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4143/1024 : ℝ)
  · exact real_three_w1093 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8287/2048 : ℝ)
  · exact real_three_w1094 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1095 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g002 p hpa hpb

#print axioms solution
