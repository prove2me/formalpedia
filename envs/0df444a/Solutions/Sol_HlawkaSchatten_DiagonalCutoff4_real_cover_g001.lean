-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g001
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:53:42.811891+00:00
-- url     : https://prove2.me/submissions/f66595b4-4725-4189-abde-4a3038196aad

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1032
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1033
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1034
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1035
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1036
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1037
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1038
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1039
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1040
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1041
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1042
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1043
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1044
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1045
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1046
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1047
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1048
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1049
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1050
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1051
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1052
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1053
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1054
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1055
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1056
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1057
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1058
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1059
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1060
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1061
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1062
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1063
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g001 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8225/2048 : ℝ)
  · exact real_three_w1032 p hpa h0
  by_cases h1 : p ≤ (4113/1024 : ℝ)
  · exact real_three_w1033 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8227/2048 : ℝ)
  · exact real_three_w1034 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2057/512 : ℝ)
  · exact real_three_w1035 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8229/2048 : ℝ)
  · exact real_three_w1036 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4115/1024 : ℝ)
  · exact real_three_w1037 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8231/2048 : ℝ)
  · exact real_three_w1038 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1029/256 : ℝ)
  · exact real_three_w1039 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8233/2048 : ℝ)
  · exact real_three_w1040 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4117/1024 : ℝ)
  · exact real_three_w1041 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8235/2048 : ℝ)
  · exact real_three_w1042 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2059/512 : ℝ)
  · exact real_three_w1043 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8237/2048 : ℝ)
  · exact real_three_w1044 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4119/1024 : ℝ)
  · exact real_three_w1045 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8239/2048 : ℝ)
  · exact real_three_w1046 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (515/128 : ℝ)
  · exact real_three_w1047 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8241/2048 : ℝ)
  · exact real_three_w1048 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4121/1024 : ℝ)
  · exact real_three_w1049 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8243/2048 : ℝ)
  · exact real_three_w1050 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2061/512 : ℝ)
  · exact real_three_w1051 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8245/2048 : ℝ)
  · exact real_three_w1052 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4123/1024 : ℝ)
  · exact real_three_w1053 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8247/2048 : ℝ)
  · exact real_three_w1054 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1031/256 : ℝ)
  · exact real_three_w1055 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8249/2048 : ℝ)
  · exact real_three_w1056 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4125/1024 : ℝ)
  · exact real_three_w1057 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8251/2048 : ℝ)
  · exact real_three_w1058 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2063/512 : ℝ)
  · exact real_three_w1059 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8253/2048 : ℝ)
  · exact real_three_w1060 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4127/1024 : ℝ)
  · exact real_three_w1061 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8255/2048 : ℝ)
  · exact real_three_w1062 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1063 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g001 p hpa hpb

#print axioms solution
