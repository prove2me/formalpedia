-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g011
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:13:30.638932+00:00
-- url     : https://prove2.me/submissions/93585ac7-ad48-4542-a1a5-6ec1d79f821c

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1352
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1353
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1354
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1355
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1356
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1357
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1358
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1359
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1360
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1361
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1362
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1363
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1364
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1365
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1366
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1367
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1368
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1369
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1370
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1371
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1372
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1373
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1374
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1375
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1376
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1377
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1378
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1379
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1380
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1381
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1382
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1383
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g011 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (539/128 : ℝ)
  · exact real_three_w1352 p hpa h0
  by_cases h1 : p ≤ (4313/1024 : ℝ)
  · exact real_three_w1353 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (2157/512 : ℝ)
  · exact real_three_w1354 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4315/1024 : ℝ)
  · exact real_three_w1355 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (1079/256 : ℝ)
  · exact real_three_w1356 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4317/1024 : ℝ)
  · exact real_three_w1357 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (2159/512 : ℝ)
  · exact real_three_w1358 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4319/1024 : ℝ)
  · exact real_three_w1359 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (135/32 : ℝ)
  · exact real_three_w1360 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4321/1024 : ℝ)
  · exact real_three_w1361 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (2161/512 : ℝ)
  · exact real_three_w1362 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4323/1024 : ℝ)
  · exact real_three_w1363 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (1081/256 : ℝ)
  · exact real_three_w1364 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4325/1024 : ℝ)
  · exact real_three_w1365 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (2163/512 : ℝ)
  · exact real_three_w1366 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4327/1024 : ℝ)
  · exact real_three_w1367 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (541/128 : ℝ)
  · exact real_three_w1368 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4329/1024 : ℝ)
  · exact real_three_w1369 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (2165/512 : ℝ)
  · exact real_three_w1370 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4331/1024 : ℝ)
  · exact real_three_w1371 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (1083/256 : ℝ)
  · exact real_three_w1372 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4333/1024 : ℝ)
  · exact real_three_w1373 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (2167/512 : ℝ)
  · exact real_three_w1374 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4335/1024 : ℝ)
  · exact real_three_w1375 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (271/64 : ℝ)
  · exact real_three_w1376 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4337/1024 : ℝ)
  · exact real_three_w1377 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (2169/512 : ℝ)
  · exact real_three_w1378 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4339/1024 : ℝ)
  · exact real_three_w1379 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (1085/256 : ℝ)
  · exact real_three_w1380 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4341/1024 : ℝ)
  · exact real_three_w1381 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (2171/512 : ℝ)
  · exact real_three_w1382 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1383 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g011 p hpa hpb

#print axioms solution
