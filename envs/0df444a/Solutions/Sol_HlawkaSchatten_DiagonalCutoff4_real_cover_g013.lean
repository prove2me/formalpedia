-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g013
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:38:42.160898+00:00
-- url     : https://prove2.me/submissions/888fbd45-f6aa-4286-ab73-f12c21dd3d5e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1416
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1417
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1418
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1419
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1420
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1421
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1422
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1423
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1424
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1425
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1426
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1427
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1428
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1429
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1430
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1431
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1432
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1433
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1434
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1435
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1436
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1437
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1438
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1439
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1440
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1441
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1442
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1443
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1444
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1445
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1446
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1447
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g013 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (547/128 : ℝ)
  · exact real_three_w1416 p hpa h0
  by_cases h1 : p ≤ (4377/1024 : ℝ)
  · exact real_three_w1417 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (2189/512 : ℝ)
  · exact real_three_w1418 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4379/1024 : ℝ)
  · exact real_three_w1419 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (1095/256 : ℝ)
  · exact real_three_w1420 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4381/1024 : ℝ)
  · exact real_three_w1421 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (2191/512 : ℝ)
  · exact real_three_w1422 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4383/1024 : ℝ)
  · exact real_three_w1423 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (137/32 : ℝ)
  · exact real_three_w1424 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4385/1024 : ℝ)
  · exact real_three_w1425 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (2193/512 : ℝ)
  · exact real_three_w1426 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4387/1024 : ℝ)
  · exact real_three_w1427 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (1097/256 : ℝ)
  · exact real_three_w1428 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4389/1024 : ℝ)
  · exact real_three_w1429 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (2195/512 : ℝ)
  · exact real_three_w1430 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4391/1024 : ℝ)
  · exact real_three_w1431 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (549/128 : ℝ)
  · exact real_three_w1432 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4393/1024 : ℝ)
  · exact real_three_w1433 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (2197/512 : ℝ)
  · exact real_three_w1434 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4395/1024 : ℝ)
  · exact real_three_w1435 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (1099/256 : ℝ)
  · exact real_three_w1436 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4397/1024 : ℝ)
  · exact real_three_w1437 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (2199/512 : ℝ)
  · exact real_three_w1438 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4399/1024 : ℝ)
  · exact real_three_w1439 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (275/64 : ℝ)
  · exact real_three_w1440 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4401/1024 : ℝ)
  · exact real_three_w1441 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (2201/512 : ℝ)
  · exact real_three_w1442 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4403/1024 : ℝ)
  · exact real_three_w1443 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (1101/256 : ℝ)
  · exact real_three_w1444 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4405/1024 : ℝ)
  · exact real_three_w1445 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (2203/512 : ℝ)
  · exact real_three_w1446 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1447 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g013 p hpa hpb

#print axioms solution
