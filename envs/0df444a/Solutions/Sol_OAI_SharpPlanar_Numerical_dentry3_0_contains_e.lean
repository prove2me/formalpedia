-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.dentry3_0_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:08:54.695664+00:00
-- url     : https://prove2.me/submissions/b38d5bd3-8c88-49a1-8a7b-b22c27600e75

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_CachedData_cm1_1_0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_D_0_e
import Theorems.Thm_OAI_SharpPlanar_D_1_e
import Theorems.Thm_OAI_SharpPlanar_D_3_e
import Theorems.Thm_OAI_SharpPlanar_D_4_e
import Theorems.Thm_OAI_SharpPlanar_D_7_e
import Theorems.Thm_OAI_SharpPlanar_D_9_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_sum_fin_square_e
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_ofReal_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_mul_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_finSum_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_complexBasis_rule_error_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma S_apply (x : X) (ni : Node × Bool) : S x ni = Scoords x ni := rfl

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma RBox.add_check (a b : RBox) : a.AddCheck b (a.add b) := ⟨le_rfl,le_rfl⟩
lemma RBox.contains_add {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := RBox.add_contains_e hx hy (RBox.add_check _ _)
lemma RBox.contains_mul {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := RBox.mul_contains_e hx hy (RBox.mul_check_e _ _)

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

lemma rcast_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (rcast a).Contains (x:ℂ) := CBox.ofReal_contains_e hx

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_periodic (n : ℕ) : phase12 (n+12) = phase12 n := by
  unfold phase12
  have he : Complex.I*Real.pi*(((n+12:ℕ):ℂ)/6) =
      Complex.I*Real.pi*((n:ℂ)/6)+2*Real.pi*Complex.I := by push_cast <;> ring
  rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic).map_mod_nat n

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma u_factored (n j : ℕ) (t : ℝ) : u n j t =
    -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) := by
  unfold u basisBeta basisAlpha spectralCoefficient
  congr 1
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring
lemma v_factored (n j : ℕ) (t : ℝ) : v n j t =
    2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j := by
  unfold v basisAlpha spectralCoefficient
  rfl

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma spectralCoefficient_eq_phase (n l : ℕ) :
    spectralCoefficient n l = Pcoeff l*phase12 (l*n) := by
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring
lemma spectralCoefficient_mod (n l : ℕ) :
    spectralCoefficient (n%12) l = spectralCoefficient n l := by
  simp only [spectralCoefficient_eq_phase]
  rw [← phase12_mod (l*(n%12)),← phase12_mod (l*n)]
  congr 2
  simp only [Nat.mul_mod, Nat.mod_mod]
lemma basisAlpha_mod (n j : ℕ) : basisAlpha (n%12) j = basisAlpha n j := by
  unfold basisAlpha
  simp only [spectralCoefficient_mod]
lemma basisBeta_mod (n j : ℕ) : basisBeta (n%12) j = basisBeta n j := by
  unfold basisBeta
  simp only [spectralCoefficient_mod]

lemma pointLambda_eq (t : ℝ) : pointLambda t = lambda t := by
  unfold pointLambda lambda b h
  push_cast
  rfl
lemma pointZ_eq (t : ℝ) : pointZ t = z t := by
  unfold pointZ z B h
  push_cast
  rfl

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow0_contains (j : Fin 6) : (aRow0 j).Contains (basisAlpha 0 j.val) := by
  fin_cases j
  · exact a0_0_contains_e
  · exact a0_1_contains_e
  · exact a0_2_contains_e
  · exact a0_3_contains_e
  · exact a0_4_contains_e
  · exact a0_5_contains_e
lemma bRow0_contains (j : Fin 6) : (bRow0 j).Contains (basisBeta 0 j.val) := by
  fin_cases j
  · exact b0_0_contains_e
  · exact b0_1_contains_e
  · exact b0_2_contains_e
  · exact b0_3_contains_e
  · exact b0_4_contains_e
  · exact b0_5_contains_e
lemma aRow1_contains (j : Fin 6) : (aRow1 j).Contains (basisAlpha 1 j.val) := by
  fin_cases j
  · exact a1_0_contains_e
  · exact a1_1_contains_e
  · exact a1_2_contains_e
  · exact a1_3_contains_e
  · exact a1_4_contains_e
  · exact a1_5_contains_e
lemma bRow1_contains (j : Fin 6) : (bRow1 j).Contains (basisBeta 1 j.val) := by
  fin_cases j
  · exact b1_0_contains_e
  · exact b1_1_contains_e
  · exact b1_2_contains_e
  · exact b1_3_contains_e
  · exact b1_4_contains_e
  · exact b1_5_contains_e
lemma aRow2_contains (j : Fin 6) : (aRow2 j).Contains (basisAlpha 2 j.val) := by
  fin_cases j
  · exact a2_0_contains_e
  · exact a2_1_contains_e
  · exact a2_2_contains_e
  · exact a2_3_contains_e
  · exact a2_4_contains_e
  · exact a2_5_contains_e
lemma bRow2_contains (j : Fin 6) : (bRow2 j).Contains (basisBeta 2 j.val) := by
  fin_cases j
  · exact b2_0_contains_e
  · exact b2_1_contains_e
  · exact b2_2_contains_e
  · exact b2_3_contains_e
  · exact b2_4_contains_e
  · exact b2_5_contains_e
lemma aRow3_contains (j : Fin 6) : (aRow3 j).Contains (basisAlpha 3 j.val) := by
  fin_cases j
  · exact a3_0_contains_e
  · exact a3_1_contains_e
  · exact a3_2_contains_e
  · exact a3_3_contains_e
  · exact a3_4_contains_e
  · exact a3_5_contains_e
lemma bRow3_contains (j : Fin 6) : (bRow3 j).Contains (basisBeta 3 j.val) := by
  fin_cases j
  · exact b3_0_contains_e
  · exact b3_1_contains_e
  · exact b3_2_contains_e
  · exact b3_3_contains_e
  · exact b3_4_contains_e
  · exact b3_5_contains_e
lemma aRow4_contains (j : Fin 6) : (aRow4 j).Contains (basisAlpha 4 j.val) := by
  fin_cases j
  · exact a4_0_contains_e
  · exact a4_1_contains_e
  · exact a4_2_contains_e
  · exact a4_3_contains_e
  · exact a4_4_contains_e
  · exact a4_5_contains_e
lemma bRow4_contains (j : Fin 6) : (bRow4 j).Contains (basisBeta 4 j.val) := by
  fin_cases j
  · exact b4_0_contains_e
  · exact b4_1_contains_e
  · exact b4_2_contains_e
  · exact b4_3_contains_e
  · exact b4_4_contains_e
  · exact b4_5_contains_e
lemma aRow5_contains (j : Fin 6) : (aRow5 j).Contains (basisAlpha 5 j.val) := by
  fin_cases j
  · exact a5_0_contains_e
  · exact a5_1_contains_e
  · exact a5_2_contains_e
  · exact a5_3_contains_e
  · exact a5_4_contains_e
  · exact a5_5_contains_e
lemma bRow5_contains (j : Fin 6) : (bRow5 j).Contains (basisBeta 5 j.val) := by
  fin_cases j
  · exact b5_0_contains_e
  · exact b5_1_contains_e
  · exact b5_2_contains_e
  · exact b5_3_contains_e
  · exact b5_4_contains_e
  · exact b5_5_contains_e
lemma aRow6_contains (j : Fin 6) : (aRow6 j).Contains (basisAlpha 6 j.val) := by
  fin_cases j
  · exact a6_0_contains_e
  · exact a6_1_contains_e
  · exact a6_2_contains_e
  · exact a6_3_contains_e
  · exact a6_4_contains_e
  · exact a6_5_contains_e
lemma bRow6_contains (j : Fin 6) : (bRow6 j).Contains (basisBeta 6 j.val) := by
  fin_cases j
  · exact b6_0_contains_e
  · exact b6_1_contains_e
  · exact b6_2_contains_e
  · exact b6_3_contains_e
  · exact b6_4_contains_e
  · exact b6_5_contains_e
lemma aRow7_contains (j : Fin 6) : (aRow7 j).Contains (basisAlpha 7 j.val) := by
  fin_cases j
  · exact a7_0_contains_e
  · exact a7_1_contains_e
  · exact a7_2_contains_e
  · exact a7_3_contains_e
  · exact a7_4_contains_e
  · exact a7_5_contains_e
lemma bRow7_contains (j : Fin 6) : (bRow7 j).Contains (basisBeta 7 j.val) := by
  fin_cases j
  · exact b7_0_contains_e
  · exact b7_1_contains_e
  · exact b7_2_contains_e
  · exact b7_3_contains_e
  · exact b7_4_contains_e
  · exact b7_5_contains_e
lemma aRow8_contains (j : Fin 6) : (aRow8 j).Contains (basisAlpha 8 j.val) := by
  fin_cases j
  · exact a8_0_contains_e
  · exact a8_1_contains_e
  · exact a8_2_contains_e
  · exact a8_3_contains_e
  · exact a8_4_contains_e
  · exact a8_5_contains_e
lemma bRow8_contains (j : Fin 6) : (bRow8 j).Contains (basisBeta 8 j.val) := by
  fin_cases j
  · exact b8_0_contains_e
  · exact b8_1_contains_e
  · exact b8_2_contains_e
  · exact b8_3_contains_e
  · exact b8_4_contains_e
  · exact b8_5_contains_e
lemma aRow9_contains (j : Fin 6) : (aRow9 j).Contains (basisAlpha 9 j.val) := by
  fin_cases j
  · exact a9_0_contains_e
  · exact a9_1_contains_e
  · exact a9_2_contains_e
  · exact a9_3_contains_e
  · exact a9_4_contains_e
  · exact a9_5_contains_e
lemma bRow9_contains (j : Fin 6) : (bRow9 j).Contains (basisBeta 9 j.val) := by
  fin_cases j
  · exact b9_0_contains_e
  · exact b9_1_contains_e
  · exact b9_2_contains_e
  · exact b9_3_contains_e
  · exact b9_4_contains_e
  · exact b9_5_contains_e
lemma aRow10_contains (j : Fin 6) : (aRow10 j).Contains (basisAlpha 10 j.val) := by
  fin_cases j
  · exact a10_0_contains_e
  · exact a10_1_contains_e
  · exact a10_2_contains_e
  · exact a10_3_contains_e
  · exact a10_4_contains_e
  · exact a10_5_contains_e
lemma bRow10_contains (j : Fin 6) : (bRow10 j).Contains (basisBeta 10 j.val) := by
  fin_cases j
  · exact b10_0_contains_e
  · exact b10_1_contains_e
  · exact b10_2_contains_e
  · exact b10_3_contains_e
  · exact b10_4_contains_e
  · exact b10_5_contains_e
lemma aRow11_contains (j : Fin 6) : (aRow11 j).Contains (basisAlpha 11 j.val) := by
  fin_cases j
  · exact a11_0_contains_e
  · exact a11_1_contains_e
  · exact a11_2_contains_e
  · exact a11_3_contains_e
  · exact a11_4_contains_e
  · exact a11_5_contains_e
lemma bRow11_contains (j : Fin 6) : (bRow11 j).Contains (basisBeta 11 j.val) := by
  fin_cases j
  · exact b11_0_contains_e
  · exact b11_1_contains_e
  · exact b11_2_contains_e
  · exact b11_3_contains_e
  · exact b11_4_contains_e
  · exact b11_5_contains_e
lemma aTable_contains (n : Fin 12) (j : Fin 6) : (aTable n j).Contains (basisAlpha n.val j.val) := by
  fin_cases n
  · exact aRow0_contains j
  · exact aRow1_contains j
  · exact aRow2_contains j
  · exact aRow3_contains j
  · exact aRow4_contains j
  · exact aRow5_contains j
  · exact aRow6_contains j
  · exact aRow7_contains j
  · exact aRow8_contains j
  · exact aRow9_contains j
  · exact aRow10_contains j
  · exact aRow11_contains j
lemma aLookup_contains (n : ℕ) (j : Fin 6) : (aLookup n j).Contains (basisAlpha n j.val) := by
  simpa only [aLookup,basisAlpha_mod] using aTable_contains ⟨n%12,by omega⟩ j
lemma bTable_contains (n : Fin 12) (j : Fin 6) : (bTable n j).Contains (basisBeta n.val j.val) := by
  fin_cases n
  · exact bRow0_contains j
  · exact bRow1_contains j
  · exact bRow2_contains j
  · exact bRow3_contains j
  · exact bRow4_contains j
  · exact bRow5_contains j
  · exact bRow6_contains j
  · exact bRow7_contains j
  · exact bRow8_contains j
  · exact bRow9_contains j
  · exact bRow10_contains j
  · exact bRow11_contains j
lemma bLookup_contains (n : ℕ) (j : Fin 6) : (bLookup n j).Contains (basisBeta n j.val) := by
  simpa only [bLookup,basisBeta_mod] using bTable_contains ⟨n%12,by omega⟩ j
end SharpPlanar.IntegerAlpha

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma cachedMomentRuleBox_contains
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox} {t : ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    {n m : ℕ} {d e : Bool}
    (hc : ∀ j i v, (c j i v).Contains ((w (16*i.val+v.val):ℂ)*
      basisFunction d n j.val (t j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains
      (lambda (t j.val (16*i.val+v.val))*Complex.exp (Complex.I*Real.pi*z (t j.val (16*i.val+v.val))*m)*
      (if e then Complex.I*Real.pi*z (t j.val (16*i.val+v.val)) else 1))) :
    (cachedMomentRuleBox c k).Contains (momentRuleValue t w n m d e) := by
  unfold cachedMomentRuleBox momentRuleValue
  apply finSum_contains_e
  intro j
  rw [← sum_fin_square_e 16 (fun v => (w v:ℂ)*basisMoment d e n j.val m (t j.val v))]
  have hh := finSum_contains_e (fun i => finSum_contains_e (fun v => CBox.contains_mul_e (hc j i v) (hk j i v)))
  have hs := CBox.contains_scale_e hh 1 6 (by norm_num)
  simpa only [Int.cast_one,Int.cast_ofNat,basisMoment,mul_assoc] using hs

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerAlpha IntegerCompact

lemma complexU_ofReal (n j : ℕ) (t : ℝ) : complexU n j t = u n j t := rfl
lemma complexV_ofReal (n j : ℕ) (t : ℝ) : complexV n j t = v n j t := rfl
lemma complexLambda_ofReal (t : ℝ) : complexLambda t = lambda t := rfl
lemma complexZ_ofReal (t : ℝ) : complexZ t = z t := rfl
lemma complexBasisMoment_ofReal (d e : Bool) (n j m : ℕ) (t : ℝ) :
    complexBasisMoment d e n j m t = basisMoment d e n j m t := by
  unfold complexBasisMoment complexBasis basisMoment basisFunction complexTransformedFactor
  rw [complexU_ofReal,complexV_ofReal,complexLambda_ofReal,complexZ_ofReal]
  cases d <;> cases e <;> simp <;> ring


end SharpPlanar

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_direct_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (-Complex.I*Real.pi*t*n)))
    (hq : q.Contains (Complex.exp (-Complex.I*Real.pi*t))) :
    (p.mul q).Contains (Complex.exp (-Complex.I*Real.pi*t*(n+1))) := by
  have hh := CBox.contains_mul_e hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring
lemma exp_transformed_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (Complex.I*Real.pi*z t*n)))
    (hq : q.Contains (Complex.exp (Complex.I*Real.pi*z t))) :
    (p.mul q).Contains (Complex.exp (Complex.I*Real.pi*z t*(n+1))) := by
  have hh := CBox.contains_mul_e hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma transformedStepBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) :
    (transformedStepBox p).Contains (Complex.exp (Complex.I*Real.pi*z t)) := by
  have hh := CBox.contains_powFast_e hp.2.2.2.2 3 4 (by norm_num)
  rw [← Complex.exp_nat_mul] at hh
  change (p.quarter.powFast 3 4).Contains _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [pointZ_eq]
  congr 1
  push_cast
  ring

lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod,basisBeta_mod]
lemma basisFunction_wave (d : Bool) (n j : ℕ) (t : ℝ) :
    basisFunction d n j t = waveAmplitude d n j t*Complex.exp (-Complex.I*Real.pi*t*n) := by
  cases d <;> simp only [basisFunction,waveAmplitude,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · rw [u_factored]; ring
  · rw [v_factored]; ring
lemma waveAmplitudeBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t)
    {a b : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j))
    (hb : b.Contains (basisBeta n j)) (d : Bool) :
    (waveAmplitudeBox p a b d).Contains (waveAmplitude d n j t) := by
  cases d
  · have hh := CBox.contains_mul_e
      (CBox.contains_scale_e (CBox.contains_mul_e (rcast_contains piBounds_contains_e)
        (rcast_contains piBounds_contains_e)) (-2) 1 (by norm_num))
      (CBox.contains_add_e hb (CBox.neg_contains_e (CBox.contains_mul_e (rcast_contains hp.1) ha)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,Bool.false_eq_true,ite_false, if_false,Int.cast_neg,Int.cast_ofNat,Int.cast_one] <;> ring)
  · have hh := CBox.contains_mul_e (CBox.contains_scale_e piI_contains_e 2 1 (by norm_num)) ha
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,ite_true, if_true,Int.cast_ofNat,Int.cast_one] <;> ring)

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quadrature enclosures for cardinal moments

The certified quadrature grid and cardinal basis enclosures bound the finite moment rule.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerAlpha IntegerGrid IntegerCompact

lemma basis_rule_value (n m : ℕ) (d e : Bool) :
    (∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val) =
      momentRuleValue quadraturePoint fejerWeight n m d e := by
  unfold pieceRule momentRuleValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have ht : diskAffine j.val (fejerNode v.val) = (quadraturePoint j.val v.val:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  rw [ht,complexBasisMoment_ofReal]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma amp1_00_0_eq : ∀ k : Fin 16, amp1_0Expr 0 0 k = amp1_00_0 k := by decide +kernel
lemma amp1_00_1_eq : ∀ k : Fin 16, amp1_0Expr 0 1 k = amp1_00_1 k := by decide +kernel
lemma amp1_00_2_eq : ∀ k : Fin 16, amp1_0Expr 0 2 k = amp1_00_2 k := by decide +kernel
lemma amp1_00_3_eq : ∀ k : Fin 16, amp1_0Expr 0 3 k = amp1_00_3 k := by decide +kernel
lemma amp1_00_4_eq : ∀ k : Fin 16, amp1_0Expr 0 4 k = amp1_00_4 k := by decide +kernel
lemma amp1_00_5_eq : ∀ k : Fin 16, amp1_0Expr 0 5 k = amp1_00_5 k := by decide +kernel
lemma amp1_00_6_eq : ∀ k : Fin 16, amp1_0Expr 0 6 k = amp1_00_6 k := by decide +kernel
lemma amp1_00_7_eq : ∀ k : Fin 16, amp1_0Expr 0 7 k = amp1_00_7 k := by decide +kernel
lemma amp1_00_8_eq : ∀ k : Fin 16, amp1_0Expr 0 8 k = amp1_00_8 k := by decide +kernel
lemma amp1_00_9_eq : ∀ k : Fin 16, amp1_0Expr 0 9 k = amp1_00_9 k := by decide +kernel
lemma amp1_00_10_eq : ∀ k : Fin 16, amp1_0Expr 0 10 k = amp1_00_10 k := by decide +kernel
lemma amp1_00_11_eq : ∀ k : Fin 16, amp1_0Expr 0 11 k = amp1_00_11 k := by decide +kernel
lemma amp1_00_12_eq : ∀ k : Fin 16, amp1_0Expr 0 12 k = amp1_00_12 k := by decide +kernel
lemma amp1_00_13_eq : ∀ k : Fin 16, amp1_0Expr 0 13 k = amp1_00_13 k := by decide +kernel
lemma amp1_00_14_eq : ∀ k : Fin 16, amp1_0Expr 0 14 k = amp1_00_14 k := by decide +kernel
lemma amp1_00_15_eq : ∀ k : Fin 16, amp1_0Expr 0 15 k = amp1_00_15 k := by decide +kernel
lemma amp1_00_eq (i k : Fin 16) : amp1_0Expr 0 i k = amp1_00 i k := by
  fin_cases i
  · exact amp1_00_0_eq k
  · exact amp1_00_1_eq k
  · exact amp1_00_2_eq k
  · exact amp1_00_3_eq k
  · exact amp1_00_4_eq k
  · exact amp1_00_5_eq k
  · exact amp1_00_6_eq k
  · exact amp1_00_7_eq k
  · exact amp1_00_8_eq k
  · exact amp1_00_9_eq k
  · exact amp1_00_10_eq k
  · exact amp1_00_11_eq k
  · exact amp1_00_12_eq k
  · exact amp1_00_13_eq k
  · exact amp1_00_14_eq k
  · exact amp1_00_15_eq k
lemma amp1_01_0_eq : ∀ k : Fin 16, amp1_0Expr 1 0 k = amp1_01_0 k := by decide +kernel
lemma amp1_01_1_eq : ∀ k : Fin 16, amp1_0Expr 1 1 k = amp1_01_1 k := by decide +kernel
lemma amp1_01_2_eq : ∀ k : Fin 16, amp1_0Expr 1 2 k = amp1_01_2 k := by decide +kernel
lemma amp1_01_3_eq : ∀ k : Fin 16, amp1_0Expr 1 3 k = amp1_01_3 k := by decide +kernel
lemma amp1_01_4_eq : ∀ k : Fin 16, amp1_0Expr 1 4 k = amp1_01_4 k := by decide +kernel
lemma amp1_01_5_eq : ∀ k : Fin 16, amp1_0Expr 1 5 k = amp1_01_5 k := by decide +kernel
lemma amp1_01_6_eq : ∀ k : Fin 16, amp1_0Expr 1 6 k = amp1_01_6 k := by decide +kernel
lemma amp1_01_7_eq : ∀ k : Fin 16, amp1_0Expr 1 7 k = amp1_01_7 k := by decide +kernel
lemma amp1_01_8_eq : ∀ k : Fin 16, amp1_0Expr 1 8 k = amp1_01_8 k := by decide +kernel
lemma amp1_01_9_eq : ∀ k : Fin 16, amp1_0Expr 1 9 k = amp1_01_9 k := by decide +kernel
lemma amp1_01_10_eq : ∀ k : Fin 16, amp1_0Expr 1 10 k = amp1_01_10 k := by decide +kernel
lemma amp1_01_11_eq : ∀ k : Fin 16, amp1_0Expr 1 11 k = amp1_01_11 k := by decide +kernel
lemma amp1_01_12_eq : ∀ k : Fin 16, amp1_0Expr 1 12 k = amp1_01_12 k := by decide +kernel
lemma amp1_01_13_eq : ∀ k : Fin 16, amp1_0Expr 1 13 k = amp1_01_13 k := by decide +kernel
lemma amp1_01_14_eq : ∀ k : Fin 16, amp1_0Expr 1 14 k = amp1_01_14 k := by decide +kernel
lemma amp1_01_15_eq : ∀ k : Fin 16, amp1_0Expr 1 15 k = amp1_01_15 k := by decide +kernel
lemma amp1_01_eq (i k : Fin 16) : amp1_0Expr 1 i k = amp1_01 i k := by
  fin_cases i
  · exact amp1_01_0_eq k
  · exact amp1_01_1_eq k
  · exact amp1_01_2_eq k
  · exact amp1_01_3_eq k
  · exact amp1_01_4_eq k
  · exact amp1_01_5_eq k
  · exact amp1_01_6_eq k
  · exact amp1_01_7_eq k
  · exact amp1_01_8_eq k
  · exact amp1_01_9_eq k
  · exact amp1_01_10_eq k
  · exact amp1_01_11_eq k
  · exact amp1_01_12_eq k
  · exact amp1_01_13_eq k
  · exact amp1_01_14_eq k
  · exact amp1_01_15_eq k
lemma amp1_02_0_eq : ∀ k : Fin 16, amp1_0Expr 2 0 k = amp1_02_0 k := by decide +kernel
lemma amp1_02_1_eq : ∀ k : Fin 16, amp1_0Expr 2 1 k = amp1_02_1 k := by decide +kernel
lemma amp1_02_2_eq : ∀ k : Fin 16, amp1_0Expr 2 2 k = amp1_02_2 k := by decide +kernel
lemma amp1_02_3_eq : ∀ k : Fin 16, amp1_0Expr 2 3 k = amp1_02_3 k := by decide +kernel
lemma amp1_02_4_eq : ∀ k : Fin 16, amp1_0Expr 2 4 k = amp1_02_4 k := by decide +kernel
lemma amp1_02_5_eq : ∀ k : Fin 16, amp1_0Expr 2 5 k = amp1_02_5 k := by decide +kernel
lemma amp1_02_6_eq : ∀ k : Fin 16, amp1_0Expr 2 6 k = amp1_02_6 k := by decide +kernel
lemma amp1_02_7_eq : ∀ k : Fin 16, amp1_0Expr 2 7 k = amp1_02_7 k := by decide +kernel
lemma amp1_02_8_eq : ∀ k : Fin 16, amp1_0Expr 2 8 k = amp1_02_8 k := by decide +kernel
lemma amp1_02_9_eq : ∀ k : Fin 16, amp1_0Expr 2 9 k = amp1_02_9 k := by decide +kernel
lemma amp1_02_10_eq : ∀ k : Fin 16, amp1_0Expr 2 10 k = amp1_02_10 k := by decide +kernel
lemma amp1_02_11_eq : ∀ k : Fin 16, amp1_0Expr 2 11 k = amp1_02_11 k := by decide +kernel
lemma amp1_02_12_eq : ∀ k : Fin 16, amp1_0Expr 2 12 k = amp1_02_12 k := by decide +kernel
lemma amp1_02_13_eq : ∀ k : Fin 16, amp1_0Expr 2 13 k = amp1_02_13 k := by decide +kernel
lemma amp1_02_14_eq : ∀ k : Fin 16, amp1_0Expr 2 14 k = amp1_02_14 k := by decide +kernel
lemma amp1_02_15_eq : ∀ k : Fin 16, amp1_0Expr 2 15 k = amp1_02_15 k := by decide +kernel
lemma amp1_02_eq (i k : Fin 16) : amp1_0Expr 2 i k = amp1_02 i k := by
  fin_cases i
  · exact amp1_02_0_eq k
  · exact amp1_02_1_eq k
  · exact amp1_02_2_eq k
  · exact amp1_02_3_eq k
  · exact amp1_02_4_eq k
  · exact amp1_02_5_eq k
  · exact amp1_02_6_eq k
  · exact amp1_02_7_eq k
  · exact amp1_02_8_eq k
  · exact amp1_02_9_eq k
  · exact amp1_02_10_eq k
  · exact amp1_02_11_eq k
  · exact amp1_02_12_eq k
  · exact amp1_02_13_eq k
  · exact amp1_02_14_eq k
  · exact amp1_02_15_eq k
lemma amp1_03_0_eq : ∀ k : Fin 16, amp1_0Expr 3 0 k = amp1_03_0 k := by decide +kernel
lemma amp1_03_1_eq : ∀ k : Fin 16, amp1_0Expr 3 1 k = amp1_03_1 k := by decide +kernel
lemma amp1_03_2_eq : ∀ k : Fin 16, amp1_0Expr 3 2 k = amp1_03_2 k := by decide +kernel
lemma amp1_03_3_eq : ∀ k : Fin 16, amp1_0Expr 3 3 k = amp1_03_3 k := by decide +kernel
lemma amp1_03_4_eq : ∀ k : Fin 16, amp1_0Expr 3 4 k = amp1_03_4 k := by decide +kernel
lemma amp1_03_5_eq : ∀ k : Fin 16, amp1_0Expr 3 5 k = amp1_03_5 k := by decide +kernel
lemma amp1_03_6_eq : ∀ k : Fin 16, amp1_0Expr 3 6 k = amp1_03_6 k := by decide +kernel
lemma amp1_03_7_eq : ∀ k : Fin 16, amp1_0Expr 3 7 k = amp1_03_7 k := by decide +kernel
lemma amp1_03_8_eq : ∀ k : Fin 16, amp1_0Expr 3 8 k = amp1_03_8 k := by decide +kernel
lemma amp1_03_9_eq : ∀ k : Fin 16, amp1_0Expr 3 9 k = amp1_03_9 k := by decide +kernel
lemma amp1_03_10_eq : ∀ k : Fin 16, amp1_0Expr 3 10 k = amp1_03_10 k := by decide +kernel
lemma amp1_03_11_eq : ∀ k : Fin 16, amp1_0Expr 3 11 k = amp1_03_11 k := by decide +kernel
lemma amp1_03_12_eq : ∀ k : Fin 16, amp1_0Expr 3 12 k = amp1_03_12 k := by decide +kernel
lemma amp1_03_13_eq : ∀ k : Fin 16, amp1_0Expr 3 13 k = amp1_03_13 k := by decide +kernel
lemma amp1_03_14_eq : ∀ k : Fin 16, amp1_0Expr 3 14 k = amp1_03_14 k := by decide +kernel
lemma amp1_03_15_eq : ∀ k : Fin 16, amp1_0Expr 3 15 k = amp1_03_15 k := by decide +kernel
lemma amp1_03_eq (i k : Fin 16) : amp1_0Expr 3 i k = amp1_03 i k := by
  fin_cases i
  · exact amp1_03_0_eq k
  · exact amp1_03_1_eq k
  · exact amp1_03_2_eq k
  · exact amp1_03_3_eq k
  · exact amp1_03_4_eq k
  · exact amp1_03_5_eq k
  · exact amp1_03_6_eq k
  · exact amp1_03_7_eq k
  · exact amp1_03_8_eq k
  · exact amp1_03_9_eq k
  · exact amp1_03_10_eq k
  · exact amp1_03_11_eq k
  · exact amp1_03_12_eq k
  · exact amp1_03_13_eq k
  · exact amp1_03_14_eq k
  · exact amp1_03_15_eq k
lemma amp1_04_0_eq : ∀ k : Fin 16, amp1_0Expr 4 0 k = amp1_04_0 k := by decide +kernel
lemma amp1_04_1_eq : ∀ k : Fin 16, amp1_0Expr 4 1 k = amp1_04_1 k := by decide +kernel
lemma amp1_04_2_eq : ∀ k : Fin 16, amp1_0Expr 4 2 k = amp1_04_2 k := by decide +kernel
lemma amp1_04_3_eq : ∀ k : Fin 16, amp1_0Expr 4 3 k = amp1_04_3 k := by decide +kernel
lemma amp1_04_4_eq : ∀ k : Fin 16, amp1_0Expr 4 4 k = amp1_04_4 k := by decide +kernel
lemma amp1_04_5_eq : ∀ k : Fin 16, amp1_0Expr 4 5 k = amp1_04_5 k := by decide +kernel
lemma amp1_04_6_eq : ∀ k : Fin 16, amp1_0Expr 4 6 k = amp1_04_6 k := by decide +kernel
lemma amp1_04_7_eq : ∀ k : Fin 16, amp1_0Expr 4 7 k = amp1_04_7 k := by decide +kernel
lemma amp1_04_8_eq : ∀ k : Fin 16, amp1_0Expr 4 8 k = amp1_04_8 k := by decide +kernel
lemma amp1_04_9_eq : ∀ k : Fin 16, amp1_0Expr 4 9 k = amp1_04_9 k := by decide +kernel
lemma amp1_04_10_eq : ∀ k : Fin 16, amp1_0Expr 4 10 k = amp1_04_10 k := by decide +kernel
lemma amp1_04_11_eq : ∀ k : Fin 16, amp1_0Expr 4 11 k = amp1_04_11 k := by decide +kernel
lemma amp1_04_12_eq : ∀ k : Fin 16, amp1_0Expr 4 12 k = amp1_04_12 k := by decide +kernel
lemma amp1_04_13_eq : ∀ k : Fin 16, amp1_0Expr 4 13 k = amp1_04_13 k := by decide +kernel
lemma amp1_04_14_eq : ∀ k : Fin 16, amp1_0Expr 4 14 k = amp1_04_14 k := by decide +kernel
lemma amp1_04_15_eq : ∀ k : Fin 16, amp1_0Expr 4 15 k = amp1_04_15 k := by decide +kernel
lemma amp1_04_eq (i k : Fin 16) : amp1_0Expr 4 i k = amp1_04 i k := by
  fin_cases i
  · exact amp1_04_0_eq k
  · exact amp1_04_1_eq k
  · exact amp1_04_2_eq k
  · exact amp1_04_3_eq k
  · exact amp1_04_4_eq k
  · exact amp1_04_5_eq k
  · exact amp1_04_6_eq k
  · exact amp1_04_7_eq k
  · exact amp1_04_8_eq k
  · exact amp1_04_9_eq k
  · exact amp1_04_10_eq k
  · exact amp1_04_11_eq k
  · exact amp1_04_12_eq k
  · exact amp1_04_13_eq k
  · exact amp1_04_14_eq k
  · exact amp1_04_15_eq k
lemma amp1_05_0_eq : ∀ k : Fin 16, amp1_0Expr 5 0 k = amp1_05_0 k := by decide +kernel
lemma amp1_05_1_eq : ∀ k : Fin 16, amp1_0Expr 5 1 k = amp1_05_1 k := by decide +kernel
lemma amp1_05_2_eq : ∀ k : Fin 16, amp1_0Expr 5 2 k = amp1_05_2 k := by decide +kernel
lemma amp1_05_3_eq : ∀ k : Fin 16, amp1_0Expr 5 3 k = amp1_05_3 k := by decide +kernel
lemma amp1_05_4_eq : ∀ k : Fin 16, amp1_0Expr 5 4 k = amp1_05_4 k := by decide +kernel
lemma amp1_05_5_eq : ∀ k : Fin 16, amp1_0Expr 5 5 k = amp1_05_5 k := by decide +kernel
lemma amp1_05_6_eq : ∀ k : Fin 16, amp1_0Expr 5 6 k = amp1_05_6 k := by decide +kernel
lemma amp1_05_7_eq : ∀ k : Fin 16, amp1_0Expr 5 7 k = amp1_05_7 k := by decide +kernel
lemma amp1_05_8_eq : ∀ k : Fin 16, amp1_0Expr 5 8 k = amp1_05_8 k := by decide +kernel
lemma amp1_05_9_eq : ∀ k : Fin 16, amp1_0Expr 5 9 k = amp1_05_9 k := by decide +kernel
lemma amp1_05_10_eq : ∀ k : Fin 16, amp1_0Expr 5 10 k = amp1_05_10 k := by decide +kernel
lemma amp1_05_11_eq : ∀ k : Fin 16, amp1_0Expr 5 11 k = amp1_05_11 k := by decide +kernel
lemma amp1_05_12_eq : ∀ k : Fin 16, amp1_0Expr 5 12 k = amp1_05_12 k := by decide +kernel
lemma amp1_05_13_eq : ∀ k : Fin 16, amp1_0Expr 5 13 k = amp1_05_13 k := by decide +kernel
lemma amp1_05_14_eq : ∀ k : Fin 16, amp1_0Expr 5 14 k = amp1_05_14 k := by decide +kernel
lemma amp1_05_15_eq : ∀ k : Fin 16, amp1_0Expr 5 15 k = amp1_05_15 k := by decide +kernel
lemma amp1_05_eq (i k : Fin 16) : amp1_0Expr 5 i k = amp1_05 i k := by
  fin_cases i
  · exact amp1_05_0_eq k
  · exact amp1_05_1_eq k
  · exact amp1_05_2_eq k
  · exact amp1_05_3_eq k
  · exact amp1_05_4_eq k
  · exact amp1_05_5_eq k
  · exact amp1_05_6_eq k
  · exact amp1_05_7_eq k
  · exact amp1_05_8_eq k
  · exact amp1_05_9_eq k
  · exact amp1_05_10_eq k
  · exact amp1_05_11_eq k
  · exact amp1_05_12_eq k
  · exact amp1_05_13_eq k
  · exact amp1_05_14_eq k
  · exact amp1_05_15_eq k
lemma amp1_0_eq (j : Fin 6) (i k : Fin 16) : amp1_0Expr j i k = amp1_0 j i k := by
  fin_cases j
  · exact amp1_00_eq i k
  · exact amp1_01_eq i k
  · exact amp1_02_eq i k
  · exact amp1_03_eq i k
  · exact amp1_04_eq i k
  · exact amp1_05_eq i k
lemma amp1_0_contains (j : Fin 6) (i k : Fin 16) :
    (amp1_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude false 1 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp1_0_eq]
  exact CBox.contains_mul_e (rcast_contains (weightRows_contains_e i k))
    (waveAmplitudeBox_contains (gridRows_contains_e j i k) (aLookup_contains 1 j) (bLookup_contains 1 j) false)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power0_contains (j : Fin 6) (i k : Fin 16) :
    (power0 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(0:ℕ))) := by
  simpa only [power0,Nat.cast_zero,mul_zero,Complex.exp_zero,Int.cast_one,one_div,inv_one,Int.cast_zero,zero_div,mul_zero,zero_mul,add_zero] using
    (CBox.contains_rat_e 1 1 0 1 (by norm_num) (by norm_num))
lemma power1_r0_0_eq : ∀ k : Fin 16, power1Expr 0 0 k = power1_r0_0 k := by decide +kernel
lemma power1_r0_1_eq : ∀ k : Fin 16, power1Expr 0 1 k = power1_r0_1 k := by decide +kernel
lemma power1_r0_2_eq : ∀ k : Fin 16, power1Expr 0 2 k = power1_r0_2 k := by decide +kernel
lemma power1_r0_3_eq : ∀ k : Fin 16, power1Expr 0 3 k = power1_r0_3 k := by decide +kernel
lemma power1_r0_4_eq : ∀ k : Fin 16, power1Expr 0 4 k = power1_r0_4 k := by decide +kernel
lemma power1_r0_5_eq : ∀ k : Fin 16, power1Expr 0 5 k = power1_r0_5 k := by decide +kernel
lemma power1_r0_6_eq : ∀ k : Fin 16, power1Expr 0 6 k = power1_r0_6 k := by decide +kernel
lemma power1_r0_7_eq : ∀ k : Fin 16, power1Expr 0 7 k = power1_r0_7 k := by decide +kernel
lemma power1_r0_8_eq : ∀ k : Fin 16, power1Expr 0 8 k = power1_r0_8 k := by decide +kernel
lemma power1_r0_9_eq : ∀ k : Fin 16, power1Expr 0 9 k = power1_r0_9 k := by decide +kernel
lemma power1_r0_10_eq : ∀ k : Fin 16, power1Expr 0 10 k = power1_r0_10 k := by decide +kernel
lemma power1_r0_11_eq : ∀ k : Fin 16, power1Expr 0 11 k = power1_r0_11 k := by decide +kernel
lemma power1_r0_12_eq : ∀ k : Fin 16, power1Expr 0 12 k = power1_r0_12 k := by decide +kernel
lemma power1_r0_13_eq : ∀ k : Fin 16, power1Expr 0 13 k = power1_r0_13 k := by decide +kernel
lemma power1_r0_14_eq : ∀ k : Fin 16, power1Expr 0 14 k = power1_r0_14 k := by decide +kernel
lemma power1_r0_15_eq : ∀ k : Fin 16, power1Expr 0 15 k = power1_r0_15 k := by decide +kernel
lemma power1_r0_eq (i k : Fin 16) : power1Expr 0 i k = power1_r0 i k := by
  fin_cases i
  · exact power1_r0_0_eq k
  · exact power1_r0_1_eq k
  · exact power1_r0_2_eq k
  · exact power1_r0_3_eq k
  · exact power1_r0_4_eq k
  · exact power1_r0_5_eq k
  · exact power1_r0_6_eq k
  · exact power1_r0_7_eq k
  · exact power1_r0_8_eq k
  · exact power1_r0_9_eq k
  · exact power1_r0_10_eq k
  · exact power1_r0_11_eq k
  · exact power1_r0_12_eq k
  · exact power1_r0_13_eq k
  · exact power1_r0_14_eq k
  · exact power1_r0_15_eq k
lemma power1_r1_0_eq : ∀ k : Fin 16, power1Expr 1 0 k = power1_r1_0 k := by decide +kernel
lemma power1_r1_1_eq : ∀ k : Fin 16, power1Expr 1 1 k = power1_r1_1 k := by decide +kernel
lemma power1_r1_2_eq : ∀ k : Fin 16, power1Expr 1 2 k = power1_r1_2 k := by decide +kernel
lemma power1_r1_3_eq : ∀ k : Fin 16, power1Expr 1 3 k = power1_r1_3 k := by decide +kernel
lemma power1_r1_4_eq : ∀ k : Fin 16, power1Expr 1 4 k = power1_r1_4 k := by decide +kernel
lemma power1_r1_5_eq : ∀ k : Fin 16, power1Expr 1 5 k = power1_r1_5 k := by decide +kernel
lemma power1_r1_6_eq : ∀ k : Fin 16, power1Expr 1 6 k = power1_r1_6 k := by decide +kernel
lemma power1_r1_7_eq : ∀ k : Fin 16, power1Expr 1 7 k = power1_r1_7 k := by decide +kernel
lemma power1_r1_8_eq : ∀ k : Fin 16, power1Expr 1 8 k = power1_r1_8 k := by decide +kernel
lemma power1_r1_9_eq : ∀ k : Fin 16, power1Expr 1 9 k = power1_r1_9 k := by decide +kernel
lemma power1_r1_10_eq : ∀ k : Fin 16, power1Expr 1 10 k = power1_r1_10 k := by decide +kernel
lemma power1_r1_11_eq : ∀ k : Fin 16, power1Expr 1 11 k = power1_r1_11 k := by decide +kernel
lemma power1_r1_12_eq : ∀ k : Fin 16, power1Expr 1 12 k = power1_r1_12 k := by decide +kernel
lemma power1_r1_13_eq : ∀ k : Fin 16, power1Expr 1 13 k = power1_r1_13 k := by decide +kernel
lemma power1_r1_14_eq : ∀ k : Fin 16, power1Expr 1 14 k = power1_r1_14 k := by decide +kernel
lemma power1_r1_15_eq : ∀ k : Fin 16, power1Expr 1 15 k = power1_r1_15 k := by decide +kernel
lemma power1_r1_eq (i k : Fin 16) : power1Expr 1 i k = power1_r1 i k := by
  fin_cases i
  · exact power1_r1_0_eq k
  · exact power1_r1_1_eq k
  · exact power1_r1_2_eq k
  · exact power1_r1_3_eq k
  · exact power1_r1_4_eq k
  · exact power1_r1_5_eq k
  · exact power1_r1_6_eq k
  · exact power1_r1_7_eq k
  · exact power1_r1_8_eq k
  · exact power1_r1_9_eq k
  · exact power1_r1_10_eq k
  · exact power1_r1_11_eq k
  · exact power1_r1_12_eq k
  · exact power1_r1_13_eq k
  · exact power1_r1_14_eq k
  · exact power1_r1_15_eq k
lemma power1_r2_0_eq : ∀ k : Fin 16, power1Expr 2 0 k = power1_r2_0 k := by decide +kernel
lemma power1_r2_1_eq : ∀ k : Fin 16, power1Expr 2 1 k = power1_r2_1 k := by decide +kernel
lemma power1_r2_2_eq : ∀ k : Fin 16, power1Expr 2 2 k = power1_r2_2 k := by decide +kernel
lemma power1_r2_3_eq : ∀ k : Fin 16, power1Expr 2 3 k = power1_r2_3 k := by decide +kernel
lemma power1_r2_4_eq : ∀ k : Fin 16, power1Expr 2 4 k = power1_r2_4 k := by decide +kernel
lemma power1_r2_5_eq : ∀ k : Fin 16, power1Expr 2 5 k = power1_r2_5 k := by decide +kernel
lemma power1_r2_6_eq : ∀ k : Fin 16, power1Expr 2 6 k = power1_r2_6 k := by decide +kernel
lemma power1_r2_7_eq : ∀ k : Fin 16, power1Expr 2 7 k = power1_r2_7 k := by decide +kernel
lemma power1_r2_8_eq : ∀ k : Fin 16, power1Expr 2 8 k = power1_r2_8 k := by decide +kernel
lemma power1_r2_9_eq : ∀ k : Fin 16, power1Expr 2 9 k = power1_r2_9 k := by decide +kernel
lemma power1_r2_10_eq : ∀ k : Fin 16, power1Expr 2 10 k = power1_r2_10 k := by decide +kernel
lemma power1_r2_11_eq : ∀ k : Fin 16, power1Expr 2 11 k = power1_r2_11 k := by decide +kernel
lemma power1_r2_12_eq : ∀ k : Fin 16, power1Expr 2 12 k = power1_r2_12 k := by decide +kernel
lemma power1_r2_13_eq : ∀ k : Fin 16, power1Expr 2 13 k = power1_r2_13 k := by decide +kernel
lemma power1_r2_14_eq : ∀ k : Fin 16, power1Expr 2 14 k = power1_r2_14 k := by decide +kernel
lemma power1_r2_15_eq : ∀ k : Fin 16, power1Expr 2 15 k = power1_r2_15 k := by decide +kernel
lemma power1_r2_eq (i k : Fin 16) : power1Expr 2 i k = power1_r2 i k := by
  fin_cases i
  · exact power1_r2_0_eq k
  · exact power1_r2_1_eq k
  · exact power1_r2_2_eq k
  · exact power1_r2_3_eq k
  · exact power1_r2_4_eq k
  · exact power1_r2_5_eq k
  · exact power1_r2_6_eq k
  · exact power1_r2_7_eq k
  · exact power1_r2_8_eq k
  · exact power1_r2_9_eq k
  · exact power1_r2_10_eq k
  · exact power1_r2_11_eq k
  · exact power1_r2_12_eq k
  · exact power1_r2_13_eq k
  · exact power1_r2_14_eq k
  · exact power1_r2_15_eq k
lemma power1_r3_0_eq : ∀ k : Fin 16, power1Expr 3 0 k = power1_r3_0 k := by decide +kernel
lemma power1_r3_1_eq : ∀ k : Fin 16, power1Expr 3 1 k = power1_r3_1 k := by decide +kernel
lemma power1_r3_2_eq : ∀ k : Fin 16, power1Expr 3 2 k = power1_r3_2 k := by decide +kernel
lemma power1_r3_3_eq : ∀ k : Fin 16, power1Expr 3 3 k = power1_r3_3 k := by decide +kernel
lemma power1_r3_4_eq : ∀ k : Fin 16, power1Expr 3 4 k = power1_r3_4 k := by decide +kernel
lemma power1_r3_5_eq : ∀ k : Fin 16, power1Expr 3 5 k = power1_r3_5 k := by decide +kernel
lemma power1_r3_6_eq : ∀ k : Fin 16, power1Expr 3 6 k = power1_r3_6 k := by decide +kernel
lemma power1_r3_7_eq : ∀ k : Fin 16, power1Expr 3 7 k = power1_r3_7 k := by decide +kernel
lemma power1_r3_8_eq : ∀ k : Fin 16, power1Expr 3 8 k = power1_r3_8 k := by decide +kernel
lemma power1_r3_9_eq : ∀ k : Fin 16, power1Expr 3 9 k = power1_r3_9 k := by decide +kernel
lemma power1_r3_10_eq : ∀ k : Fin 16, power1Expr 3 10 k = power1_r3_10 k := by decide +kernel
lemma power1_r3_11_eq : ∀ k : Fin 16, power1Expr 3 11 k = power1_r3_11 k := by decide +kernel
lemma power1_r3_12_eq : ∀ k : Fin 16, power1Expr 3 12 k = power1_r3_12 k := by decide +kernel
lemma power1_r3_13_eq : ∀ k : Fin 16, power1Expr 3 13 k = power1_r3_13 k := by decide +kernel
lemma power1_r3_14_eq : ∀ k : Fin 16, power1Expr 3 14 k = power1_r3_14 k := by decide +kernel
lemma power1_r3_15_eq : ∀ k : Fin 16, power1Expr 3 15 k = power1_r3_15 k := by decide +kernel
lemma power1_r3_eq (i k : Fin 16) : power1Expr 3 i k = power1_r3 i k := by
  fin_cases i
  · exact power1_r3_0_eq k
  · exact power1_r3_1_eq k
  · exact power1_r3_2_eq k
  · exact power1_r3_3_eq k
  · exact power1_r3_4_eq k
  · exact power1_r3_5_eq k
  · exact power1_r3_6_eq k
  · exact power1_r3_7_eq k
  · exact power1_r3_8_eq k
  · exact power1_r3_9_eq k
  · exact power1_r3_10_eq k
  · exact power1_r3_11_eq k
  · exact power1_r3_12_eq k
  · exact power1_r3_13_eq k
  · exact power1_r3_14_eq k
  · exact power1_r3_15_eq k
lemma power1_r4_0_eq : ∀ k : Fin 16, power1Expr 4 0 k = power1_r4_0 k := by decide +kernel
lemma power1_r4_1_eq : ∀ k : Fin 16, power1Expr 4 1 k = power1_r4_1 k := by decide +kernel
lemma power1_r4_2_eq : ∀ k : Fin 16, power1Expr 4 2 k = power1_r4_2 k := by decide +kernel
lemma power1_r4_3_eq : ∀ k : Fin 16, power1Expr 4 3 k = power1_r4_3 k := by decide +kernel
lemma power1_r4_4_eq : ∀ k : Fin 16, power1Expr 4 4 k = power1_r4_4 k := by decide +kernel
lemma power1_r4_5_eq : ∀ k : Fin 16, power1Expr 4 5 k = power1_r4_5 k := by decide +kernel
lemma power1_r4_6_eq : ∀ k : Fin 16, power1Expr 4 6 k = power1_r4_6 k := by decide +kernel
lemma power1_r4_7_eq : ∀ k : Fin 16, power1Expr 4 7 k = power1_r4_7 k := by decide +kernel
lemma power1_r4_8_eq : ∀ k : Fin 16, power1Expr 4 8 k = power1_r4_8 k := by decide +kernel
lemma power1_r4_9_eq : ∀ k : Fin 16, power1Expr 4 9 k = power1_r4_9 k := by decide +kernel
lemma power1_r4_10_eq : ∀ k : Fin 16, power1Expr 4 10 k = power1_r4_10 k := by decide +kernel
lemma power1_r4_11_eq : ∀ k : Fin 16, power1Expr 4 11 k = power1_r4_11 k := by decide +kernel
lemma power1_r4_12_eq : ∀ k : Fin 16, power1Expr 4 12 k = power1_r4_12 k := by decide +kernel
lemma power1_r4_13_eq : ∀ k : Fin 16, power1Expr 4 13 k = power1_r4_13 k := by decide +kernel
lemma power1_r4_14_eq : ∀ k : Fin 16, power1Expr 4 14 k = power1_r4_14 k := by decide +kernel
lemma power1_r4_15_eq : ∀ k : Fin 16, power1Expr 4 15 k = power1_r4_15 k := by decide +kernel
lemma power1_r4_eq (i k : Fin 16) : power1Expr 4 i k = power1_r4 i k := by
  fin_cases i
  · exact power1_r4_0_eq k
  · exact power1_r4_1_eq k
  · exact power1_r4_2_eq k
  · exact power1_r4_3_eq k
  · exact power1_r4_4_eq k
  · exact power1_r4_5_eq k
  · exact power1_r4_6_eq k
  · exact power1_r4_7_eq k
  · exact power1_r4_8_eq k
  · exact power1_r4_9_eq k
  · exact power1_r4_10_eq k
  · exact power1_r4_11_eq k
  · exact power1_r4_12_eq k
  · exact power1_r4_13_eq k
  · exact power1_r4_14_eq k
  · exact power1_r4_15_eq k
lemma power1_r5_0_eq : ∀ k : Fin 16, power1Expr 5 0 k = power1_r5_0 k := by decide +kernel
lemma power1_r5_1_eq : ∀ k : Fin 16, power1Expr 5 1 k = power1_r5_1 k := by decide +kernel
lemma power1_r5_2_eq : ∀ k : Fin 16, power1Expr 5 2 k = power1_r5_2 k := by decide +kernel
lemma power1_r5_3_eq : ∀ k : Fin 16, power1Expr 5 3 k = power1_r5_3 k := by decide +kernel
lemma power1_r5_4_eq : ∀ k : Fin 16, power1Expr 5 4 k = power1_r5_4 k := by decide +kernel
lemma power1_r5_5_eq : ∀ k : Fin 16, power1Expr 5 5 k = power1_r5_5 k := by decide +kernel
lemma power1_r5_6_eq : ∀ k : Fin 16, power1Expr 5 6 k = power1_r5_6 k := by decide +kernel
lemma power1_r5_7_eq : ∀ k : Fin 16, power1Expr 5 7 k = power1_r5_7 k := by decide +kernel
lemma power1_r5_8_eq : ∀ k : Fin 16, power1Expr 5 8 k = power1_r5_8 k := by decide +kernel
lemma power1_r5_9_eq : ∀ k : Fin 16, power1Expr 5 9 k = power1_r5_9 k := by decide +kernel
lemma power1_r5_10_eq : ∀ k : Fin 16, power1Expr 5 10 k = power1_r5_10 k := by decide +kernel
lemma power1_r5_11_eq : ∀ k : Fin 16, power1Expr 5 11 k = power1_r5_11 k := by decide +kernel
lemma power1_r5_12_eq : ∀ k : Fin 16, power1Expr 5 12 k = power1_r5_12 k := by decide +kernel
lemma power1_r5_13_eq : ∀ k : Fin 16, power1Expr 5 13 k = power1_r5_13 k := by decide +kernel
lemma power1_r5_14_eq : ∀ k : Fin 16, power1Expr 5 14 k = power1_r5_14 k := by decide +kernel
lemma power1_r5_15_eq : ∀ k : Fin 16, power1Expr 5 15 k = power1_r5_15 k := by decide +kernel
lemma power1_r5_eq (i k : Fin 16) : power1Expr 5 i k = power1_r5 i k := by
  fin_cases i
  · exact power1_r5_0_eq k
  · exact power1_r5_1_eq k
  · exact power1_r5_2_eq k
  · exact power1_r5_3_eq k
  · exact power1_r5_4_eq k
  · exact power1_r5_5_eq k
  · exact power1_r5_6_eq k
  · exact power1_r5_7_eq k
  · exact power1_r5_8_eq k
  · exact power1_r5_9_eq k
  · exact power1_r5_10_eq k
  · exact power1_r5_11_eq k
  · exact power1_r5_12_eq k
  · exact power1_r5_13_eq k
  · exact power1_r5_14_eq k
  · exact power1_r5_15_eq k
lemma power1_eq (j : Fin 6) (i k : Fin 16) : power1Expr j i k = power1 j i k := by
  fin_cases j
  · exact power1_r0_eq i k
  · exact power1_r1_eq i k
  · exact power1_r2_eq i k
  · exact power1_r3_eq i k
  · exact power1_r4_eq i k
  · exact power1_r5_eq i k
lemma power1_contains (j : Fin 6) (i k : Fin 16) :
    (power1 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(1:ℕ))) := by
  rw [← power1_eq]
  unfold power1Expr
  convert exp_direct_step (power0_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column1_0_r0_0_eq : ∀ k : Fin 16, column1_0Expr 0 0 k = column1_0_r0_0 k := by decide +kernel
lemma column1_0_r0_1_eq : ∀ k : Fin 16, column1_0Expr 0 1 k = column1_0_r0_1 k := by decide +kernel
lemma column1_0_r0_2_eq : ∀ k : Fin 16, column1_0Expr 0 2 k = column1_0_r0_2 k := by decide +kernel
lemma column1_0_r0_3_eq : ∀ k : Fin 16, column1_0Expr 0 3 k = column1_0_r0_3 k := by decide +kernel
lemma column1_0_r0_4_eq : ∀ k : Fin 16, column1_0Expr 0 4 k = column1_0_r0_4 k := by decide +kernel
lemma column1_0_r0_5_eq : ∀ k : Fin 16, column1_0Expr 0 5 k = column1_0_r0_5 k := by decide +kernel
lemma column1_0_r0_6_eq : ∀ k : Fin 16, column1_0Expr 0 6 k = column1_0_r0_6 k := by decide +kernel
lemma column1_0_r0_7_eq : ∀ k : Fin 16, column1_0Expr 0 7 k = column1_0_r0_7 k := by decide +kernel
lemma column1_0_r0_8_eq : ∀ k : Fin 16, column1_0Expr 0 8 k = column1_0_r0_8 k := by decide +kernel
lemma column1_0_r0_9_eq : ∀ k : Fin 16, column1_0Expr 0 9 k = column1_0_r0_9 k := by decide +kernel
lemma column1_0_r0_10_eq : ∀ k : Fin 16, column1_0Expr 0 10 k = column1_0_r0_10 k := by decide +kernel
lemma column1_0_r0_11_eq : ∀ k : Fin 16, column1_0Expr 0 11 k = column1_0_r0_11 k := by decide +kernel
lemma column1_0_r0_12_eq : ∀ k : Fin 16, column1_0Expr 0 12 k = column1_0_r0_12 k := by decide +kernel
lemma column1_0_r0_13_eq : ∀ k : Fin 16, column1_0Expr 0 13 k = column1_0_r0_13 k := by decide +kernel
lemma column1_0_r0_14_eq : ∀ k : Fin 16, column1_0Expr 0 14 k = column1_0_r0_14 k := by decide +kernel
lemma column1_0_r0_15_eq : ∀ k : Fin 16, column1_0Expr 0 15 k = column1_0_r0_15 k := by decide +kernel
lemma column1_0_r0_eq (i k : Fin 16) : column1_0Expr 0 i k = column1_0_r0 i k := by
  fin_cases i
  · exact column1_0_r0_0_eq k
  · exact column1_0_r0_1_eq k
  · exact column1_0_r0_2_eq k
  · exact column1_0_r0_3_eq k
  · exact column1_0_r0_4_eq k
  · exact column1_0_r0_5_eq k
  · exact column1_0_r0_6_eq k
  · exact column1_0_r0_7_eq k
  · exact column1_0_r0_8_eq k
  · exact column1_0_r0_9_eq k
  · exact column1_0_r0_10_eq k
  · exact column1_0_r0_11_eq k
  · exact column1_0_r0_12_eq k
  · exact column1_0_r0_13_eq k
  · exact column1_0_r0_14_eq k
  · exact column1_0_r0_15_eq k
lemma column1_0_r1_0_eq : ∀ k : Fin 16, column1_0Expr 1 0 k = column1_0_r1_0 k := by decide +kernel
lemma column1_0_r1_1_eq : ∀ k : Fin 16, column1_0Expr 1 1 k = column1_0_r1_1 k := by decide +kernel
lemma column1_0_r1_2_eq : ∀ k : Fin 16, column1_0Expr 1 2 k = column1_0_r1_2 k := by decide +kernel
lemma column1_0_r1_3_eq : ∀ k : Fin 16, column1_0Expr 1 3 k = column1_0_r1_3 k := by decide +kernel
lemma column1_0_r1_4_eq : ∀ k : Fin 16, column1_0Expr 1 4 k = column1_0_r1_4 k := by decide +kernel
lemma column1_0_r1_5_eq : ∀ k : Fin 16, column1_0Expr 1 5 k = column1_0_r1_5 k := by decide +kernel
lemma column1_0_r1_6_eq : ∀ k : Fin 16, column1_0Expr 1 6 k = column1_0_r1_6 k := by decide +kernel
lemma column1_0_r1_7_eq : ∀ k : Fin 16, column1_0Expr 1 7 k = column1_0_r1_7 k := by decide +kernel
lemma column1_0_r1_8_eq : ∀ k : Fin 16, column1_0Expr 1 8 k = column1_0_r1_8 k := by decide +kernel
lemma column1_0_r1_9_eq : ∀ k : Fin 16, column1_0Expr 1 9 k = column1_0_r1_9 k := by decide +kernel
lemma column1_0_r1_10_eq : ∀ k : Fin 16, column1_0Expr 1 10 k = column1_0_r1_10 k := by decide +kernel
lemma column1_0_r1_11_eq : ∀ k : Fin 16, column1_0Expr 1 11 k = column1_0_r1_11 k := by decide +kernel
lemma column1_0_r1_12_eq : ∀ k : Fin 16, column1_0Expr 1 12 k = column1_0_r1_12 k := by decide +kernel
lemma column1_0_r1_13_eq : ∀ k : Fin 16, column1_0Expr 1 13 k = column1_0_r1_13 k := by decide +kernel
lemma column1_0_r1_14_eq : ∀ k : Fin 16, column1_0Expr 1 14 k = column1_0_r1_14 k := by decide +kernel
lemma column1_0_r1_15_eq : ∀ k : Fin 16, column1_0Expr 1 15 k = column1_0_r1_15 k := by decide +kernel
lemma column1_0_r1_eq (i k : Fin 16) : column1_0Expr 1 i k = column1_0_r1 i k := by
  fin_cases i
  · exact column1_0_r1_0_eq k
  · exact column1_0_r1_1_eq k
  · exact column1_0_r1_2_eq k
  · exact column1_0_r1_3_eq k
  · exact column1_0_r1_4_eq k
  · exact column1_0_r1_5_eq k
  · exact column1_0_r1_6_eq k
  · exact column1_0_r1_7_eq k
  · exact column1_0_r1_8_eq k
  · exact column1_0_r1_9_eq k
  · exact column1_0_r1_10_eq k
  · exact column1_0_r1_11_eq k
  · exact column1_0_r1_12_eq k
  · exact column1_0_r1_13_eq k
  · exact column1_0_r1_14_eq k
  · exact column1_0_r1_15_eq k
lemma column1_0_r2_0_eq : ∀ k : Fin 16, column1_0Expr 2 0 k = column1_0_r2_0 k := by decide +kernel
lemma column1_0_r2_1_eq : ∀ k : Fin 16, column1_0Expr 2 1 k = column1_0_r2_1 k := by decide +kernel
lemma column1_0_r2_2_eq : ∀ k : Fin 16, column1_0Expr 2 2 k = column1_0_r2_2 k := by decide +kernel
lemma column1_0_r2_3_eq : ∀ k : Fin 16, column1_0Expr 2 3 k = column1_0_r2_3 k := by decide +kernel
lemma column1_0_r2_4_eq : ∀ k : Fin 16, column1_0Expr 2 4 k = column1_0_r2_4 k := by decide +kernel
lemma column1_0_r2_5_eq : ∀ k : Fin 16, column1_0Expr 2 5 k = column1_0_r2_5 k := by decide +kernel
lemma column1_0_r2_6_eq : ∀ k : Fin 16, column1_0Expr 2 6 k = column1_0_r2_6 k := by decide +kernel
lemma column1_0_r2_7_eq : ∀ k : Fin 16, column1_0Expr 2 7 k = column1_0_r2_7 k := by decide +kernel
lemma column1_0_r2_8_eq : ∀ k : Fin 16, column1_0Expr 2 8 k = column1_0_r2_8 k := by decide +kernel
lemma column1_0_r2_9_eq : ∀ k : Fin 16, column1_0Expr 2 9 k = column1_0_r2_9 k := by decide +kernel
lemma column1_0_r2_10_eq : ∀ k : Fin 16, column1_0Expr 2 10 k = column1_0_r2_10 k := by decide +kernel
lemma column1_0_r2_11_eq : ∀ k : Fin 16, column1_0Expr 2 11 k = column1_0_r2_11 k := by decide +kernel
lemma column1_0_r2_12_eq : ∀ k : Fin 16, column1_0Expr 2 12 k = column1_0_r2_12 k := by decide +kernel
lemma column1_0_r2_13_eq : ∀ k : Fin 16, column1_0Expr 2 13 k = column1_0_r2_13 k := by decide +kernel
lemma column1_0_r2_14_eq : ∀ k : Fin 16, column1_0Expr 2 14 k = column1_0_r2_14 k := by decide +kernel
lemma column1_0_r2_15_eq : ∀ k : Fin 16, column1_0Expr 2 15 k = column1_0_r2_15 k := by decide +kernel
lemma column1_0_r2_eq (i k : Fin 16) : column1_0Expr 2 i k = column1_0_r2 i k := by
  fin_cases i
  · exact column1_0_r2_0_eq k
  · exact column1_0_r2_1_eq k
  · exact column1_0_r2_2_eq k
  · exact column1_0_r2_3_eq k
  · exact column1_0_r2_4_eq k
  · exact column1_0_r2_5_eq k
  · exact column1_0_r2_6_eq k
  · exact column1_0_r2_7_eq k
  · exact column1_0_r2_8_eq k
  · exact column1_0_r2_9_eq k
  · exact column1_0_r2_10_eq k
  · exact column1_0_r2_11_eq k
  · exact column1_0_r2_12_eq k
  · exact column1_0_r2_13_eq k
  · exact column1_0_r2_14_eq k
  · exact column1_0_r2_15_eq k
lemma column1_0_r3_0_eq : ∀ k : Fin 16, column1_0Expr 3 0 k = column1_0_r3_0 k := by decide +kernel
lemma column1_0_r3_1_eq : ∀ k : Fin 16, column1_0Expr 3 1 k = column1_0_r3_1 k := by decide +kernel
lemma column1_0_r3_2_eq : ∀ k : Fin 16, column1_0Expr 3 2 k = column1_0_r3_2 k := by decide +kernel
lemma column1_0_r3_3_eq : ∀ k : Fin 16, column1_0Expr 3 3 k = column1_0_r3_3 k := by decide +kernel
lemma column1_0_r3_4_eq : ∀ k : Fin 16, column1_0Expr 3 4 k = column1_0_r3_4 k := by decide +kernel
lemma column1_0_r3_5_eq : ∀ k : Fin 16, column1_0Expr 3 5 k = column1_0_r3_5 k := by decide +kernel
lemma column1_0_r3_6_eq : ∀ k : Fin 16, column1_0Expr 3 6 k = column1_0_r3_6 k := by decide +kernel
lemma column1_0_r3_7_eq : ∀ k : Fin 16, column1_0Expr 3 7 k = column1_0_r3_7 k := by decide +kernel
lemma column1_0_r3_8_eq : ∀ k : Fin 16, column1_0Expr 3 8 k = column1_0_r3_8 k := by decide +kernel
lemma column1_0_r3_9_eq : ∀ k : Fin 16, column1_0Expr 3 9 k = column1_0_r3_9 k := by decide +kernel
lemma column1_0_r3_10_eq : ∀ k : Fin 16, column1_0Expr 3 10 k = column1_0_r3_10 k := by decide +kernel
lemma column1_0_r3_11_eq : ∀ k : Fin 16, column1_0Expr 3 11 k = column1_0_r3_11 k := by decide +kernel
lemma column1_0_r3_12_eq : ∀ k : Fin 16, column1_0Expr 3 12 k = column1_0_r3_12 k := by decide +kernel
lemma column1_0_r3_13_eq : ∀ k : Fin 16, column1_0Expr 3 13 k = column1_0_r3_13 k := by decide +kernel
lemma column1_0_r3_14_eq : ∀ k : Fin 16, column1_0Expr 3 14 k = column1_0_r3_14 k := by decide +kernel
lemma column1_0_r3_15_eq : ∀ k : Fin 16, column1_0Expr 3 15 k = column1_0_r3_15 k := by decide +kernel
lemma column1_0_r3_eq (i k : Fin 16) : column1_0Expr 3 i k = column1_0_r3 i k := by
  fin_cases i
  · exact column1_0_r3_0_eq k
  · exact column1_0_r3_1_eq k
  · exact column1_0_r3_2_eq k
  · exact column1_0_r3_3_eq k
  · exact column1_0_r3_4_eq k
  · exact column1_0_r3_5_eq k
  · exact column1_0_r3_6_eq k
  · exact column1_0_r3_7_eq k
  · exact column1_0_r3_8_eq k
  · exact column1_0_r3_9_eq k
  · exact column1_0_r3_10_eq k
  · exact column1_0_r3_11_eq k
  · exact column1_0_r3_12_eq k
  · exact column1_0_r3_13_eq k
  · exact column1_0_r3_14_eq k
  · exact column1_0_r3_15_eq k
lemma column1_0_r4_0_eq : ∀ k : Fin 16, column1_0Expr 4 0 k = column1_0_r4_0 k := by decide +kernel
lemma column1_0_r4_1_eq : ∀ k : Fin 16, column1_0Expr 4 1 k = column1_0_r4_1 k := by decide +kernel
lemma column1_0_r4_2_eq : ∀ k : Fin 16, column1_0Expr 4 2 k = column1_0_r4_2 k := by decide +kernel
lemma column1_0_r4_3_eq : ∀ k : Fin 16, column1_0Expr 4 3 k = column1_0_r4_3 k := by decide +kernel
lemma column1_0_r4_4_eq : ∀ k : Fin 16, column1_0Expr 4 4 k = column1_0_r4_4 k := by decide +kernel
lemma column1_0_r4_5_eq : ∀ k : Fin 16, column1_0Expr 4 5 k = column1_0_r4_5 k := by decide +kernel
lemma column1_0_r4_6_eq : ∀ k : Fin 16, column1_0Expr 4 6 k = column1_0_r4_6 k := by decide +kernel
lemma column1_0_r4_7_eq : ∀ k : Fin 16, column1_0Expr 4 7 k = column1_0_r4_7 k := by decide +kernel
lemma column1_0_r4_8_eq : ∀ k : Fin 16, column1_0Expr 4 8 k = column1_0_r4_8 k := by decide +kernel
lemma column1_0_r4_9_eq : ∀ k : Fin 16, column1_0Expr 4 9 k = column1_0_r4_9 k := by decide +kernel
lemma column1_0_r4_10_eq : ∀ k : Fin 16, column1_0Expr 4 10 k = column1_0_r4_10 k := by decide +kernel
lemma column1_0_r4_11_eq : ∀ k : Fin 16, column1_0Expr 4 11 k = column1_0_r4_11 k := by decide +kernel
lemma column1_0_r4_12_eq : ∀ k : Fin 16, column1_0Expr 4 12 k = column1_0_r4_12 k := by decide +kernel
lemma column1_0_r4_13_eq : ∀ k : Fin 16, column1_0Expr 4 13 k = column1_0_r4_13 k := by decide +kernel
lemma column1_0_r4_14_eq : ∀ k : Fin 16, column1_0Expr 4 14 k = column1_0_r4_14 k := by decide +kernel
lemma column1_0_r4_15_eq : ∀ k : Fin 16, column1_0Expr 4 15 k = column1_0_r4_15 k := by decide +kernel
lemma column1_0_r4_eq (i k : Fin 16) : column1_0Expr 4 i k = column1_0_r4 i k := by
  fin_cases i
  · exact column1_0_r4_0_eq k
  · exact column1_0_r4_1_eq k
  · exact column1_0_r4_2_eq k
  · exact column1_0_r4_3_eq k
  · exact column1_0_r4_4_eq k
  · exact column1_0_r4_5_eq k
  · exact column1_0_r4_6_eq k
  · exact column1_0_r4_7_eq k
  · exact column1_0_r4_8_eq k
  · exact column1_0_r4_9_eq k
  · exact column1_0_r4_10_eq k
  · exact column1_0_r4_11_eq k
  · exact column1_0_r4_12_eq k
  · exact column1_0_r4_13_eq k
  · exact column1_0_r4_14_eq k
  · exact column1_0_r4_15_eq k
lemma column1_0_r5_0_eq : ∀ k : Fin 16, column1_0Expr 5 0 k = column1_0_r5_0 k := by decide +kernel
lemma column1_0_r5_1_eq : ∀ k : Fin 16, column1_0Expr 5 1 k = column1_0_r5_1 k := by decide +kernel
lemma column1_0_r5_2_eq : ∀ k : Fin 16, column1_0Expr 5 2 k = column1_0_r5_2 k := by decide +kernel
lemma column1_0_r5_3_eq : ∀ k : Fin 16, column1_0Expr 5 3 k = column1_0_r5_3 k := by decide +kernel
lemma column1_0_r5_4_eq : ∀ k : Fin 16, column1_0Expr 5 4 k = column1_0_r5_4 k := by decide +kernel
lemma column1_0_r5_5_eq : ∀ k : Fin 16, column1_0Expr 5 5 k = column1_0_r5_5 k := by decide +kernel
lemma column1_0_r5_6_eq : ∀ k : Fin 16, column1_0Expr 5 6 k = column1_0_r5_6 k := by decide +kernel
lemma column1_0_r5_7_eq : ∀ k : Fin 16, column1_0Expr 5 7 k = column1_0_r5_7 k := by decide +kernel
lemma column1_0_r5_8_eq : ∀ k : Fin 16, column1_0Expr 5 8 k = column1_0_r5_8 k := by decide +kernel
lemma column1_0_r5_9_eq : ∀ k : Fin 16, column1_0Expr 5 9 k = column1_0_r5_9 k := by decide +kernel
lemma column1_0_r5_10_eq : ∀ k : Fin 16, column1_0Expr 5 10 k = column1_0_r5_10 k := by decide +kernel
lemma column1_0_r5_11_eq : ∀ k : Fin 16, column1_0Expr 5 11 k = column1_0_r5_11 k := by decide +kernel
lemma column1_0_r5_12_eq : ∀ k : Fin 16, column1_0Expr 5 12 k = column1_0_r5_12 k := by decide +kernel
lemma column1_0_r5_13_eq : ∀ k : Fin 16, column1_0Expr 5 13 k = column1_0_r5_13 k := by decide +kernel
lemma column1_0_r5_14_eq : ∀ k : Fin 16, column1_0Expr 5 14 k = column1_0_r5_14 k := by decide +kernel
lemma column1_0_r5_15_eq : ∀ k : Fin 16, column1_0Expr 5 15 k = column1_0_r5_15 k := by decide +kernel
lemma column1_0_r5_eq (i k : Fin 16) : column1_0Expr 5 i k = column1_0_r5 i k := by
  fin_cases i
  · exact column1_0_r5_0_eq k
  · exact column1_0_r5_1_eq k
  · exact column1_0_r5_2_eq k
  · exact column1_0_r5_3_eq k
  · exact column1_0_r5_4_eq k
  · exact column1_0_r5_5_eq k
  · exact column1_0_r5_6_eq k
  · exact column1_0_r5_7_eq k
  · exact column1_0_r5_8_eq k
  · exact column1_0_r5_9_eq k
  · exact column1_0_r5_10_eq k
  · exact column1_0_r5_11_eq k
  · exact column1_0_r5_12_eq k
  · exact column1_0_r5_13_eq k
  · exact column1_0_r5_14_eq k
  · exact column1_0_r5_15_eq k
lemma column1_0_eq (j : Fin 6) (i k : Fin 16) : column1_0Expr j i k = column1_0 j i k := by
  fin_cases j
  · exact column1_0_r0_eq i k
  · exact column1_0_r1_eq i k
  · exact column1_0_r2_eq i k
  · exact column1_0_r3_eq i k
  · exact column1_0_r4_eq i k
  · exact column1_0_r5_eq i k
lemma column1_0_contains (j : Fin 6) (i k : Fin 16) :
    (column1_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 1 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column1_0_eq,basisFunction_wave,← mul_assoc]
  unfold column1_0Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod false 1 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp1_0_contains j i k
  · exact power1_contains j i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma transStep_r0_eq (i k : Fin 16) : transStepExpr 0 i k = transStep_r0 i k := by
  fin_cases i
  · exact transStep_r0_0_eq_e k
  · exact transStep_r0_1_eq_e k
  · exact transStep_r0_2_eq_e k
  · exact transStep_r0_3_eq_e k
  · exact transStep_r0_4_eq_e k
  · exact transStep_r0_5_eq_e k
  · exact transStep_r0_6_eq_e k
  · exact transStep_r0_7_eq_e k
  · exact transStep_r0_8_eq_e k
  · exact transStep_r0_9_eq_e k
  · exact transStep_r0_10_eq_e k
  · exact transStep_r0_11_eq_e k
  · exact transStep_r0_12_eq_e k
  · exact transStep_r0_13_eq_e k
  · exact transStep_r0_14_eq_e k
  · exact transStep_r0_15_eq_e k
lemma transStep_r1_eq (i k : Fin 16) : transStepExpr 1 i k = transStep_r1 i k := by
  fin_cases i
  · exact transStep_r1_0_eq_e k
  · exact transStep_r1_1_eq_e k
  · exact transStep_r1_2_eq_e k
  · exact transStep_r1_3_eq_e k
  · exact transStep_r1_4_eq_e k
  · exact transStep_r1_5_eq_e k
  · exact transStep_r1_6_eq_e k
  · exact transStep_r1_7_eq_e k
  · exact transStep_r1_8_eq_e k
  · exact transStep_r1_9_eq_e k
  · exact transStep_r1_10_eq_e k
  · exact transStep_r1_11_eq_e k
  · exact transStep_r1_12_eq_e k
  · exact transStep_r1_13_eq_e k
  · exact transStep_r1_14_eq_e k
  · exact transStep_r1_15_eq_e k
lemma transStep_r2_eq (i k : Fin 16) : transStepExpr 2 i k = transStep_r2 i k := by
  fin_cases i
  · exact transStep_r2_0_eq_e k
  · exact transStep_r2_1_eq_e k
  · exact transStep_r2_2_eq_e k
  · exact transStep_r2_3_eq_e k
  · exact transStep_r2_4_eq_e k
  · exact transStep_r2_5_eq_e k
  · exact transStep_r2_6_eq_e k
  · exact transStep_r2_7_eq_e k
  · exact transStep_r2_8_eq_e k
  · exact transStep_r2_9_eq_e k
  · exact transStep_r2_10_eq_e k
  · exact transStep_r2_11_eq_e k
  · exact transStep_r2_12_eq_e k
  · exact transStep_r2_13_eq_e k
  · exact transStep_r2_14_eq_e k
  · exact transStep_r2_15_eq_e k
lemma transStep_r3_eq (i k : Fin 16) : transStepExpr 3 i k = transStep_r3 i k := by
  fin_cases i
  · exact transStep_r3_0_eq_e k
  · exact transStep_r3_1_eq_e k
  · exact transStep_r3_2_eq_e k
  · exact transStep_r3_3_eq_e k
  · exact transStep_r3_4_eq_e k
  · exact transStep_r3_5_eq_e k
  · exact transStep_r3_6_eq_e k
  · exact transStep_r3_7_eq_e k
  · exact transStep_r3_8_eq_e k
  · exact transStep_r3_9_eq_e k
  · exact transStep_r3_10_eq_e k
  · exact transStep_r3_11_eq_e k
  · exact transStep_r3_12_eq_e k
  · exact transStep_r3_13_eq_e k
  · exact transStep_r3_14_eq_e k
  · exact transStep_r3_15_eq_e k
lemma transStep_r4_eq (i k : Fin 16) : transStepExpr 4 i k = transStep_r4 i k := by
  fin_cases i
  · exact transStep_r4_0_eq_e k
  · exact transStep_r4_1_eq_e k
  · exact transStep_r4_2_eq_e k
  · exact transStep_r4_3_eq_e k
  · exact transStep_r4_4_eq_e k
  · exact transStep_r4_5_eq_e k
  · exact transStep_r4_6_eq_e k
  · exact transStep_r4_7_eq_e k
  · exact transStep_r4_8_eq_e k
  · exact transStep_r4_9_eq_e k
  · exact transStep_r4_10_eq_e k
  · exact transStep_r4_11_eq_e k
  · exact transStep_r4_12_eq_e k
  · exact transStep_r4_13_eq_e k
  · exact transStep_r4_14_eq_e k
  · exact transStep_r4_15_eq_e k
lemma transStep_r5_eq (i k : Fin 16) : transStepExpr 5 i k = transStep_r5 i k := by
  fin_cases i
  · exact transStep_r5_0_eq_e k
  · exact transStep_r5_1_eq_e k
  · exact transStep_r5_2_eq_e k
  · exact transStep_r5_3_eq_e k
  · exact transStep_r5_4_eq_e k
  · exact transStep_r5_5_eq_e k
  · exact transStep_r5_6_eq_e k
  · exact transStep_r5_7_eq_e k
  · exact transStep_r5_8_eq_e k
  · exact transStep_r5_9_eq_e k
  · exact transStep_r5_10_eq_e k
  · exact transStep_r5_11_eq_e k
  · exact transStep_r5_12_eq_e k
  · exact transStep_r5_13_eq_e k
  · exact transStep_r5_14_eq_e k
  · exact transStep_r5_15_eq_e k
lemma transStep_eq (j : Fin 6) (i k : Fin 16) : transStepExpr j i k = transStep j i k := by
  fin_cases j
  · exact transStep_r0_eq i k
  · exact transStep_r1_eq i k
  · exact transStep_r2_eq i k
  · exact transStep_r3_eq i k
  · exact transStep_r4_eq i k
  · exact transStep_r5_eq i k
lemma transStep_contains (j : Fin 6) (i k : Fin 16) :
    (transStep j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)))) := by
  rw [← transStep_eq]
  exact transformedStepBox_contains (gridRows_contains_e j i k)
lemma trans0_contains (j : Fin 6) (i k : Fin 16) :
    (trans0 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(0:ℕ))) := by
  simpa only [trans0,Nat.cast_zero,mul_zero,Complex.exp_zero,Int.cast_one,one_div,inv_one,Int.cast_zero,zero_div,mul_zero,zero_mul,add_zero] using
    (CBox.contains_rat_e 1 1 0 1 (by norm_num) (by norm_num))
lemma trans1_r0_0_eq : ∀ k : Fin 16, trans1Expr 0 0 k = trans1_r0_0 k := by decide +kernel
lemma trans1_r0_1_eq : ∀ k : Fin 16, trans1Expr 0 1 k = trans1_r0_1 k := by decide +kernel
lemma trans1_r0_2_eq : ∀ k : Fin 16, trans1Expr 0 2 k = trans1_r0_2 k := by decide +kernel
lemma trans1_r0_3_eq : ∀ k : Fin 16, trans1Expr 0 3 k = trans1_r0_3 k := by decide +kernel
lemma trans1_r0_4_eq : ∀ k : Fin 16, trans1Expr 0 4 k = trans1_r0_4 k := by decide +kernel
lemma trans1_r0_5_eq : ∀ k : Fin 16, trans1Expr 0 5 k = trans1_r0_5 k := by decide +kernel
lemma trans1_r0_6_eq : ∀ k : Fin 16, trans1Expr 0 6 k = trans1_r0_6 k := by decide +kernel
lemma trans1_r0_7_eq : ∀ k : Fin 16, trans1Expr 0 7 k = trans1_r0_7 k := by decide +kernel
lemma trans1_r0_8_eq : ∀ k : Fin 16, trans1Expr 0 8 k = trans1_r0_8 k := by decide +kernel
lemma trans1_r0_9_eq : ∀ k : Fin 16, trans1Expr 0 9 k = trans1_r0_9 k := by decide +kernel
lemma trans1_r0_10_eq : ∀ k : Fin 16, trans1Expr 0 10 k = trans1_r0_10 k := by decide +kernel
lemma trans1_r0_11_eq : ∀ k : Fin 16, trans1Expr 0 11 k = trans1_r0_11 k := by decide +kernel
lemma trans1_r0_12_eq : ∀ k : Fin 16, trans1Expr 0 12 k = trans1_r0_12 k := by decide +kernel
lemma trans1_r0_13_eq : ∀ k : Fin 16, trans1Expr 0 13 k = trans1_r0_13 k := by decide +kernel
lemma trans1_r0_14_eq : ∀ k : Fin 16, trans1Expr 0 14 k = trans1_r0_14 k := by decide +kernel
lemma trans1_r0_15_eq : ∀ k : Fin 16, trans1Expr 0 15 k = trans1_r0_15 k := by decide +kernel
lemma trans1_r0_eq (i k : Fin 16) : trans1Expr 0 i k = trans1_r0 i k := by
  fin_cases i
  · exact trans1_r0_0_eq k
  · exact trans1_r0_1_eq k
  · exact trans1_r0_2_eq k
  · exact trans1_r0_3_eq k
  · exact trans1_r0_4_eq k
  · exact trans1_r0_5_eq k
  · exact trans1_r0_6_eq k
  · exact trans1_r0_7_eq k
  · exact trans1_r0_8_eq k
  · exact trans1_r0_9_eq k
  · exact trans1_r0_10_eq k
  · exact trans1_r0_11_eq k
  · exact trans1_r0_12_eq k
  · exact trans1_r0_13_eq k
  · exact trans1_r0_14_eq k
  · exact trans1_r0_15_eq k
lemma trans1_r1_0_eq : ∀ k : Fin 16, trans1Expr 1 0 k = trans1_r1_0 k := by decide +kernel
lemma trans1_r1_1_eq : ∀ k : Fin 16, trans1Expr 1 1 k = trans1_r1_1 k := by decide +kernel
lemma trans1_r1_2_eq : ∀ k : Fin 16, trans1Expr 1 2 k = trans1_r1_2 k := by decide +kernel
lemma trans1_r1_3_eq : ∀ k : Fin 16, trans1Expr 1 3 k = trans1_r1_3 k := by decide +kernel
lemma trans1_r1_4_eq : ∀ k : Fin 16, trans1Expr 1 4 k = trans1_r1_4 k := by decide +kernel
lemma trans1_r1_5_eq : ∀ k : Fin 16, trans1Expr 1 5 k = trans1_r1_5 k := by decide +kernel
lemma trans1_r1_6_eq : ∀ k : Fin 16, trans1Expr 1 6 k = trans1_r1_6 k := by decide +kernel
lemma trans1_r1_7_eq : ∀ k : Fin 16, trans1Expr 1 7 k = trans1_r1_7 k := by decide +kernel
lemma trans1_r1_8_eq : ∀ k : Fin 16, trans1Expr 1 8 k = trans1_r1_8 k := by decide +kernel
lemma trans1_r1_9_eq : ∀ k : Fin 16, trans1Expr 1 9 k = trans1_r1_9 k := by decide +kernel
lemma trans1_r1_10_eq : ∀ k : Fin 16, trans1Expr 1 10 k = trans1_r1_10 k := by decide +kernel
lemma trans1_r1_11_eq : ∀ k : Fin 16, trans1Expr 1 11 k = trans1_r1_11 k := by decide +kernel
lemma trans1_r1_12_eq : ∀ k : Fin 16, trans1Expr 1 12 k = trans1_r1_12 k := by decide +kernel
lemma trans1_r1_13_eq : ∀ k : Fin 16, trans1Expr 1 13 k = trans1_r1_13 k := by decide +kernel
lemma trans1_r1_14_eq : ∀ k : Fin 16, trans1Expr 1 14 k = trans1_r1_14 k := by decide +kernel
lemma trans1_r1_15_eq : ∀ k : Fin 16, trans1Expr 1 15 k = trans1_r1_15 k := by decide +kernel
lemma trans1_r1_eq (i k : Fin 16) : trans1Expr 1 i k = trans1_r1 i k := by
  fin_cases i
  · exact trans1_r1_0_eq k
  · exact trans1_r1_1_eq k
  · exact trans1_r1_2_eq k
  · exact trans1_r1_3_eq k
  · exact trans1_r1_4_eq k
  · exact trans1_r1_5_eq k
  · exact trans1_r1_6_eq k
  · exact trans1_r1_7_eq k
  · exact trans1_r1_8_eq k
  · exact trans1_r1_9_eq k
  · exact trans1_r1_10_eq k
  · exact trans1_r1_11_eq k
  · exact trans1_r1_12_eq k
  · exact trans1_r1_13_eq k
  · exact trans1_r1_14_eq k
  · exact trans1_r1_15_eq k
lemma trans1_r2_0_eq : ∀ k : Fin 16, trans1Expr 2 0 k = trans1_r2_0 k := by decide +kernel
lemma trans1_r2_1_eq : ∀ k : Fin 16, trans1Expr 2 1 k = trans1_r2_1 k := by decide +kernel
lemma trans1_r2_2_eq : ∀ k : Fin 16, trans1Expr 2 2 k = trans1_r2_2 k := by decide +kernel
lemma trans1_r2_3_eq : ∀ k : Fin 16, trans1Expr 2 3 k = trans1_r2_3 k := by decide +kernel
lemma trans1_r2_4_eq : ∀ k : Fin 16, trans1Expr 2 4 k = trans1_r2_4 k := by decide +kernel
lemma trans1_r2_5_eq : ∀ k : Fin 16, trans1Expr 2 5 k = trans1_r2_5 k := by decide +kernel
lemma trans1_r2_6_eq : ∀ k : Fin 16, trans1Expr 2 6 k = trans1_r2_6 k := by decide +kernel
lemma trans1_r2_7_eq : ∀ k : Fin 16, trans1Expr 2 7 k = trans1_r2_7 k := by decide +kernel
lemma trans1_r2_8_eq : ∀ k : Fin 16, trans1Expr 2 8 k = trans1_r2_8 k := by decide +kernel
lemma trans1_r2_9_eq : ∀ k : Fin 16, trans1Expr 2 9 k = trans1_r2_9 k := by decide +kernel
lemma trans1_r2_10_eq : ∀ k : Fin 16, trans1Expr 2 10 k = trans1_r2_10 k := by decide +kernel
lemma trans1_r2_11_eq : ∀ k : Fin 16, trans1Expr 2 11 k = trans1_r2_11 k := by decide +kernel
lemma trans1_r2_12_eq : ∀ k : Fin 16, trans1Expr 2 12 k = trans1_r2_12 k := by decide +kernel
lemma trans1_r2_13_eq : ∀ k : Fin 16, trans1Expr 2 13 k = trans1_r2_13 k := by decide +kernel
lemma trans1_r2_14_eq : ∀ k : Fin 16, trans1Expr 2 14 k = trans1_r2_14 k := by decide +kernel
lemma trans1_r2_15_eq : ∀ k : Fin 16, trans1Expr 2 15 k = trans1_r2_15 k := by decide +kernel
lemma trans1_r2_eq (i k : Fin 16) : trans1Expr 2 i k = trans1_r2 i k := by
  fin_cases i
  · exact trans1_r2_0_eq k
  · exact trans1_r2_1_eq k
  · exact trans1_r2_2_eq k
  · exact trans1_r2_3_eq k
  · exact trans1_r2_4_eq k
  · exact trans1_r2_5_eq k
  · exact trans1_r2_6_eq k
  · exact trans1_r2_7_eq k
  · exact trans1_r2_8_eq k
  · exact trans1_r2_9_eq k
  · exact trans1_r2_10_eq k
  · exact trans1_r2_11_eq k
  · exact trans1_r2_12_eq k
  · exact trans1_r2_13_eq k
  · exact trans1_r2_14_eq k
  · exact trans1_r2_15_eq k
lemma trans1_r3_0_eq : ∀ k : Fin 16, trans1Expr 3 0 k = trans1_r3_0 k := by decide +kernel
lemma trans1_r3_1_eq : ∀ k : Fin 16, trans1Expr 3 1 k = trans1_r3_1 k := by decide +kernel
lemma trans1_r3_2_eq : ∀ k : Fin 16, trans1Expr 3 2 k = trans1_r3_2 k := by decide +kernel
lemma trans1_r3_3_eq : ∀ k : Fin 16, trans1Expr 3 3 k = trans1_r3_3 k := by decide +kernel
lemma trans1_r3_4_eq : ∀ k : Fin 16, trans1Expr 3 4 k = trans1_r3_4 k := by decide +kernel
lemma trans1_r3_5_eq : ∀ k : Fin 16, trans1Expr 3 5 k = trans1_r3_5 k := by decide +kernel
lemma trans1_r3_6_eq : ∀ k : Fin 16, trans1Expr 3 6 k = trans1_r3_6 k := by decide +kernel
lemma trans1_r3_7_eq : ∀ k : Fin 16, trans1Expr 3 7 k = trans1_r3_7 k := by decide +kernel
lemma trans1_r3_8_eq : ∀ k : Fin 16, trans1Expr 3 8 k = trans1_r3_8 k := by decide +kernel
lemma trans1_r3_9_eq : ∀ k : Fin 16, trans1Expr 3 9 k = trans1_r3_9 k := by decide +kernel
lemma trans1_r3_10_eq : ∀ k : Fin 16, trans1Expr 3 10 k = trans1_r3_10 k := by decide +kernel
lemma trans1_r3_11_eq : ∀ k : Fin 16, trans1Expr 3 11 k = trans1_r3_11 k := by decide +kernel
lemma trans1_r3_12_eq : ∀ k : Fin 16, trans1Expr 3 12 k = trans1_r3_12 k := by decide +kernel
lemma trans1_r3_13_eq : ∀ k : Fin 16, trans1Expr 3 13 k = trans1_r3_13 k := by decide +kernel
lemma trans1_r3_14_eq : ∀ k : Fin 16, trans1Expr 3 14 k = trans1_r3_14 k := by decide +kernel
lemma trans1_r3_15_eq : ∀ k : Fin 16, trans1Expr 3 15 k = trans1_r3_15 k := by decide +kernel
lemma trans1_r3_eq (i k : Fin 16) : trans1Expr 3 i k = trans1_r3 i k := by
  fin_cases i
  · exact trans1_r3_0_eq k
  · exact trans1_r3_1_eq k
  · exact trans1_r3_2_eq k
  · exact trans1_r3_3_eq k
  · exact trans1_r3_4_eq k
  · exact trans1_r3_5_eq k
  · exact trans1_r3_6_eq k
  · exact trans1_r3_7_eq k
  · exact trans1_r3_8_eq k
  · exact trans1_r3_9_eq k
  · exact trans1_r3_10_eq k
  · exact trans1_r3_11_eq k
  · exact trans1_r3_12_eq k
  · exact trans1_r3_13_eq k
  · exact trans1_r3_14_eq k
  · exact trans1_r3_15_eq k
lemma trans1_r4_0_eq : ∀ k : Fin 16, trans1Expr 4 0 k = trans1_r4_0 k := by decide +kernel
lemma trans1_r4_1_eq : ∀ k : Fin 16, trans1Expr 4 1 k = trans1_r4_1 k := by decide +kernel
lemma trans1_r4_2_eq : ∀ k : Fin 16, trans1Expr 4 2 k = trans1_r4_2 k := by decide +kernel
lemma trans1_r4_3_eq : ∀ k : Fin 16, trans1Expr 4 3 k = trans1_r4_3 k := by decide +kernel
lemma trans1_r4_4_eq : ∀ k : Fin 16, trans1Expr 4 4 k = trans1_r4_4 k := by decide +kernel
lemma trans1_r4_5_eq : ∀ k : Fin 16, trans1Expr 4 5 k = trans1_r4_5 k := by decide +kernel
lemma trans1_r4_6_eq : ∀ k : Fin 16, trans1Expr 4 6 k = trans1_r4_6 k := by decide +kernel
lemma trans1_r4_7_eq : ∀ k : Fin 16, trans1Expr 4 7 k = trans1_r4_7 k := by decide +kernel
lemma trans1_r4_8_eq : ∀ k : Fin 16, trans1Expr 4 8 k = trans1_r4_8 k := by decide +kernel
lemma trans1_r4_9_eq : ∀ k : Fin 16, trans1Expr 4 9 k = trans1_r4_9 k := by decide +kernel
lemma trans1_r4_10_eq : ∀ k : Fin 16, trans1Expr 4 10 k = trans1_r4_10 k := by decide +kernel
lemma trans1_r4_11_eq : ∀ k : Fin 16, trans1Expr 4 11 k = trans1_r4_11 k := by decide +kernel
lemma trans1_r4_12_eq : ∀ k : Fin 16, trans1Expr 4 12 k = trans1_r4_12 k := by decide +kernel
lemma trans1_r4_13_eq : ∀ k : Fin 16, trans1Expr 4 13 k = trans1_r4_13 k := by decide +kernel
lemma trans1_r4_14_eq : ∀ k : Fin 16, trans1Expr 4 14 k = trans1_r4_14 k := by decide +kernel
lemma trans1_r4_15_eq : ∀ k : Fin 16, trans1Expr 4 15 k = trans1_r4_15 k := by decide +kernel
lemma trans1_r4_eq (i k : Fin 16) : trans1Expr 4 i k = trans1_r4 i k := by
  fin_cases i
  · exact trans1_r4_0_eq k
  · exact trans1_r4_1_eq k
  · exact trans1_r4_2_eq k
  · exact trans1_r4_3_eq k
  · exact trans1_r4_4_eq k
  · exact trans1_r4_5_eq k
  · exact trans1_r4_6_eq k
  · exact trans1_r4_7_eq k
  · exact trans1_r4_8_eq k
  · exact trans1_r4_9_eq k
  · exact trans1_r4_10_eq k
  · exact trans1_r4_11_eq k
  · exact trans1_r4_12_eq k
  · exact trans1_r4_13_eq k
  · exact trans1_r4_14_eq k
  · exact trans1_r4_15_eq k
lemma trans1_r5_0_eq : ∀ k : Fin 16, trans1Expr 5 0 k = trans1_r5_0 k := by decide +kernel
lemma trans1_r5_1_eq : ∀ k : Fin 16, trans1Expr 5 1 k = trans1_r5_1 k := by decide +kernel
lemma trans1_r5_2_eq : ∀ k : Fin 16, trans1Expr 5 2 k = trans1_r5_2 k := by decide +kernel
lemma trans1_r5_3_eq : ∀ k : Fin 16, trans1Expr 5 3 k = trans1_r5_3 k := by decide +kernel
lemma trans1_r5_4_eq : ∀ k : Fin 16, trans1Expr 5 4 k = trans1_r5_4 k := by decide +kernel
lemma trans1_r5_5_eq : ∀ k : Fin 16, trans1Expr 5 5 k = trans1_r5_5 k := by decide +kernel
lemma trans1_r5_6_eq : ∀ k : Fin 16, trans1Expr 5 6 k = trans1_r5_6 k := by decide +kernel
lemma trans1_r5_7_eq : ∀ k : Fin 16, trans1Expr 5 7 k = trans1_r5_7 k := by decide +kernel
lemma trans1_r5_8_eq : ∀ k : Fin 16, trans1Expr 5 8 k = trans1_r5_8 k := by decide +kernel
lemma trans1_r5_9_eq : ∀ k : Fin 16, trans1Expr 5 9 k = trans1_r5_9 k := by decide +kernel
lemma trans1_r5_10_eq : ∀ k : Fin 16, trans1Expr 5 10 k = trans1_r5_10 k := by decide +kernel
lemma trans1_r5_11_eq : ∀ k : Fin 16, trans1Expr 5 11 k = trans1_r5_11 k := by decide +kernel
lemma trans1_r5_12_eq : ∀ k : Fin 16, trans1Expr 5 12 k = trans1_r5_12 k := by decide +kernel
lemma trans1_r5_13_eq : ∀ k : Fin 16, trans1Expr 5 13 k = trans1_r5_13 k := by decide +kernel
lemma trans1_r5_14_eq : ∀ k : Fin 16, trans1Expr 5 14 k = trans1_r5_14 k := by decide +kernel
lemma trans1_r5_15_eq : ∀ k : Fin 16, trans1Expr 5 15 k = trans1_r5_15 k := by decide +kernel
lemma trans1_r5_eq (i k : Fin 16) : trans1Expr 5 i k = trans1_r5 i k := by
  fin_cases i
  · exact trans1_r5_0_eq k
  · exact trans1_r5_1_eq k
  · exact trans1_r5_2_eq k
  · exact trans1_r5_3_eq k
  · exact trans1_r5_4_eq k
  · exact trans1_r5_5_eq k
  · exact trans1_r5_6_eq k
  · exact trans1_r5_7_eq k
  · exact trans1_r5_8_eq k
  · exact trans1_r5_9_eq k
  · exact trans1_r5_10_eq k
  · exact trans1_r5_11_eq k
  · exact trans1_r5_12_eq k
  · exact trans1_r5_13_eq k
  · exact trans1_r5_14_eq k
  · exact trans1_r5_15_eq k
lemma trans1_eq (j : Fin 6) (i k : Fin 16) : trans1Expr j i k = trans1 j i k := by
  fin_cases j
  · exact trans1_r0_eq i k
  · exact trans1_r1_eq i k
  · exact trans1_r2_eq i k
  · exact trans1_r3_eq i k
  · exact trans1_r4_eq i k
  · exact trans1_r5_eq i k
lemma trans1_contains (j : Fin 6) (i k : Fin 16) :
    (trans1 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(1:ℕ))) := by
  rw [← trans1_eq]
  unfold trans1Expr
  convert exp_transformed_step (trans0_contains j i k) (transStep_contains j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma kernel1_0_r0_0_eq : ∀ k : Fin 16, kernel1_0Expr 0 0 k = kernel1_0_r0_0 k := by decide +kernel
lemma kernel1_0_r0_1_eq : ∀ k : Fin 16, kernel1_0Expr 0 1 k = kernel1_0_r0_1 k := by decide +kernel
lemma kernel1_0_r0_2_eq : ∀ k : Fin 16, kernel1_0Expr 0 2 k = kernel1_0_r0_2 k := by decide +kernel
lemma kernel1_0_r0_3_eq : ∀ k : Fin 16, kernel1_0Expr 0 3 k = kernel1_0_r0_3 k := by decide +kernel
lemma kernel1_0_r0_4_eq : ∀ k : Fin 16, kernel1_0Expr 0 4 k = kernel1_0_r0_4 k := by decide +kernel
lemma kernel1_0_r0_5_eq : ∀ k : Fin 16, kernel1_0Expr 0 5 k = kernel1_0_r0_5 k := by decide +kernel
lemma kernel1_0_r0_6_eq : ∀ k : Fin 16, kernel1_0Expr 0 6 k = kernel1_0_r0_6 k := by decide +kernel
lemma kernel1_0_r0_7_eq : ∀ k : Fin 16, kernel1_0Expr 0 7 k = kernel1_0_r0_7 k := by decide +kernel
lemma kernel1_0_r0_8_eq : ∀ k : Fin 16, kernel1_0Expr 0 8 k = kernel1_0_r0_8 k := by decide +kernel
lemma kernel1_0_r0_9_eq : ∀ k : Fin 16, kernel1_0Expr 0 9 k = kernel1_0_r0_9 k := by decide +kernel
lemma kernel1_0_r0_10_eq : ∀ k : Fin 16, kernel1_0Expr 0 10 k = kernel1_0_r0_10 k := by decide +kernel
lemma kernel1_0_r0_11_eq : ∀ k : Fin 16, kernel1_0Expr 0 11 k = kernel1_0_r0_11 k := by decide +kernel
lemma kernel1_0_r0_12_eq : ∀ k : Fin 16, kernel1_0Expr 0 12 k = kernel1_0_r0_12 k := by decide +kernel
lemma kernel1_0_r0_13_eq : ∀ k : Fin 16, kernel1_0Expr 0 13 k = kernel1_0_r0_13 k := by decide +kernel
lemma kernel1_0_r0_14_eq : ∀ k : Fin 16, kernel1_0Expr 0 14 k = kernel1_0_r0_14 k := by decide +kernel
lemma kernel1_0_r0_15_eq : ∀ k : Fin 16, kernel1_0Expr 0 15 k = kernel1_0_r0_15 k := by decide +kernel
lemma kernel1_0_r0_eq (i k : Fin 16) : kernel1_0Expr 0 i k = kernel1_0_r0 i k := by
  fin_cases i
  · exact kernel1_0_r0_0_eq k
  · exact kernel1_0_r0_1_eq k
  · exact kernel1_0_r0_2_eq k
  · exact kernel1_0_r0_3_eq k
  · exact kernel1_0_r0_4_eq k
  · exact kernel1_0_r0_5_eq k
  · exact kernel1_0_r0_6_eq k
  · exact kernel1_0_r0_7_eq k
  · exact kernel1_0_r0_8_eq k
  · exact kernel1_0_r0_9_eq k
  · exact kernel1_0_r0_10_eq k
  · exact kernel1_0_r0_11_eq k
  · exact kernel1_0_r0_12_eq k
  · exact kernel1_0_r0_13_eq k
  · exact kernel1_0_r0_14_eq k
  · exact kernel1_0_r0_15_eq k
lemma kernel1_0_r1_0_eq : ∀ k : Fin 16, kernel1_0Expr 1 0 k = kernel1_0_r1_0 k := by decide +kernel
lemma kernel1_0_r1_1_eq : ∀ k : Fin 16, kernel1_0Expr 1 1 k = kernel1_0_r1_1 k := by decide +kernel
lemma kernel1_0_r1_2_eq : ∀ k : Fin 16, kernel1_0Expr 1 2 k = kernel1_0_r1_2 k := by decide +kernel
lemma kernel1_0_r1_3_eq : ∀ k : Fin 16, kernel1_0Expr 1 3 k = kernel1_0_r1_3 k := by decide +kernel
lemma kernel1_0_r1_4_eq : ∀ k : Fin 16, kernel1_0Expr 1 4 k = kernel1_0_r1_4 k := by decide +kernel
lemma kernel1_0_r1_5_eq : ∀ k : Fin 16, kernel1_0Expr 1 5 k = kernel1_0_r1_5 k := by decide +kernel
lemma kernel1_0_r1_6_eq : ∀ k : Fin 16, kernel1_0Expr 1 6 k = kernel1_0_r1_6 k := by decide +kernel
lemma kernel1_0_r1_7_eq : ∀ k : Fin 16, kernel1_0Expr 1 7 k = kernel1_0_r1_7 k := by decide +kernel
lemma kernel1_0_r1_8_eq : ∀ k : Fin 16, kernel1_0Expr 1 8 k = kernel1_0_r1_8 k := by decide +kernel
lemma kernel1_0_r1_9_eq : ∀ k : Fin 16, kernel1_0Expr 1 9 k = kernel1_0_r1_9 k := by decide +kernel
lemma kernel1_0_r1_10_eq : ∀ k : Fin 16, kernel1_0Expr 1 10 k = kernel1_0_r1_10 k := by decide +kernel
lemma kernel1_0_r1_11_eq : ∀ k : Fin 16, kernel1_0Expr 1 11 k = kernel1_0_r1_11 k := by decide +kernel
lemma kernel1_0_r1_12_eq : ∀ k : Fin 16, kernel1_0Expr 1 12 k = kernel1_0_r1_12 k := by decide +kernel
lemma kernel1_0_r1_13_eq : ∀ k : Fin 16, kernel1_0Expr 1 13 k = kernel1_0_r1_13 k := by decide +kernel
lemma kernel1_0_r1_14_eq : ∀ k : Fin 16, kernel1_0Expr 1 14 k = kernel1_0_r1_14 k := by decide +kernel
lemma kernel1_0_r1_15_eq : ∀ k : Fin 16, kernel1_0Expr 1 15 k = kernel1_0_r1_15 k := by decide +kernel
lemma kernel1_0_r1_eq (i k : Fin 16) : kernel1_0Expr 1 i k = kernel1_0_r1 i k := by
  fin_cases i
  · exact kernel1_0_r1_0_eq k
  · exact kernel1_0_r1_1_eq k
  · exact kernel1_0_r1_2_eq k
  · exact kernel1_0_r1_3_eq k
  · exact kernel1_0_r1_4_eq k
  · exact kernel1_0_r1_5_eq k
  · exact kernel1_0_r1_6_eq k
  · exact kernel1_0_r1_7_eq k
  · exact kernel1_0_r1_8_eq k
  · exact kernel1_0_r1_9_eq k
  · exact kernel1_0_r1_10_eq k
  · exact kernel1_0_r1_11_eq k
  · exact kernel1_0_r1_12_eq k
  · exact kernel1_0_r1_13_eq k
  · exact kernel1_0_r1_14_eq k
  · exact kernel1_0_r1_15_eq k
lemma kernel1_0_r2_0_eq : ∀ k : Fin 16, kernel1_0Expr 2 0 k = kernel1_0_r2_0 k := by decide +kernel
lemma kernel1_0_r2_1_eq : ∀ k : Fin 16, kernel1_0Expr 2 1 k = kernel1_0_r2_1 k := by decide +kernel
lemma kernel1_0_r2_2_eq : ∀ k : Fin 16, kernel1_0Expr 2 2 k = kernel1_0_r2_2 k := by decide +kernel
lemma kernel1_0_r2_3_eq : ∀ k : Fin 16, kernel1_0Expr 2 3 k = kernel1_0_r2_3 k := by decide +kernel
lemma kernel1_0_r2_4_eq : ∀ k : Fin 16, kernel1_0Expr 2 4 k = kernel1_0_r2_4 k := by decide +kernel
lemma kernel1_0_r2_5_eq : ∀ k : Fin 16, kernel1_0Expr 2 5 k = kernel1_0_r2_5 k := by decide +kernel
lemma kernel1_0_r2_6_eq : ∀ k : Fin 16, kernel1_0Expr 2 6 k = kernel1_0_r2_6 k := by decide +kernel
lemma kernel1_0_r2_7_eq : ∀ k : Fin 16, kernel1_0Expr 2 7 k = kernel1_0_r2_7 k := by decide +kernel
lemma kernel1_0_r2_8_eq : ∀ k : Fin 16, kernel1_0Expr 2 8 k = kernel1_0_r2_8 k := by decide +kernel
lemma kernel1_0_r2_9_eq : ∀ k : Fin 16, kernel1_0Expr 2 9 k = kernel1_0_r2_9 k := by decide +kernel
lemma kernel1_0_r2_10_eq : ∀ k : Fin 16, kernel1_0Expr 2 10 k = kernel1_0_r2_10 k := by decide +kernel
lemma kernel1_0_r2_11_eq : ∀ k : Fin 16, kernel1_0Expr 2 11 k = kernel1_0_r2_11 k := by decide +kernel
lemma kernel1_0_r2_12_eq : ∀ k : Fin 16, kernel1_0Expr 2 12 k = kernel1_0_r2_12 k := by decide +kernel
lemma kernel1_0_r2_13_eq : ∀ k : Fin 16, kernel1_0Expr 2 13 k = kernel1_0_r2_13 k := by decide +kernel
lemma kernel1_0_r2_14_eq : ∀ k : Fin 16, kernel1_0Expr 2 14 k = kernel1_0_r2_14 k := by decide +kernel
lemma kernel1_0_r2_15_eq : ∀ k : Fin 16, kernel1_0Expr 2 15 k = kernel1_0_r2_15 k := by decide +kernel
lemma kernel1_0_r2_eq (i k : Fin 16) : kernel1_0Expr 2 i k = kernel1_0_r2 i k := by
  fin_cases i
  · exact kernel1_0_r2_0_eq k
  · exact kernel1_0_r2_1_eq k
  · exact kernel1_0_r2_2_eq k
  · exact kernel1_0_r2_3_eq k
  · exact kernel1_0_r2_4_eq k
  · exact kernel1_0_r2_5_eq k
  · exact kernel1_0_r2_6_eq k
  · exact kernel1_0_r2_7_eq k
  · exact kernel1_0_r2_8_eq k
  · exact kernel1_0_r2_9_eq k
  · exact kernel1_0_r2_10_eq k
  · exact kernel1_0_r2_11_eq k
  · exact kernel1_0_r2_12_eq k
  · exact kernel1_0_r2_13_eq k
  · exact kernel1_0_r2_14_eq k
  · exact kernel1_0_r2_15_eq k
lemma kernel1_0_r3_0_eq : ∀ k : Fin 16, kernel1_0Expr 3 0 k = kernel1_0_r3_0 k := by decide +kernel
lemma kernel1_0_r3_1_eq : ∀ k : Fin 16, kernel1_0Expr 3 1 k = kernel1_0_r3_1 k := by decide +kernel
lemma kernel1_0_r3_2_eq : ∀ k : Fin 16, kernel1_0Expr 3 2 k = kernel1_0_r3_2 k := by decide +kernel
lemma kernel1_0_r3_3_eq : ∀ k : Fin 16, kernel1_0Expr 3 3 k = kernel1_0_r3_3 k := by decide +kernel
lemma kernel1_0_r3_4_eq : ∀ k : Fin 16, kernel1_0Expr 3 4 k = kernel1_0_r3_4 k := by decide +kernel
lemma kernel1_0_r3_5_eq : ∀ k : Fin 16, kernel1_0Expr 3 5 k = kernel1_0_r3_5 k := by decide +kernel
lemma kernel1_0_r3_6_eq : ∀ k : Fin 16, kernel1_0Expr 3 6 k = kernel1_0_r3_6 k := by decide +kernel
lemma kernel1_0_r3_7_eq : ∀ k : Fin 16, kernel1_0Expr 3 7 k = kernel1_0_r3_7 k := by decide +kernel
lemma kernel1_0_r3_8_eq : ∀ k : Fin 16, kernel1_0Expr 3 8 k = kernel1_0_r3_8 k := by decide +kernel
lemma kernel1_0_r3_9_eq : ∀ k : Fin 16, kernel1_0Expr 3 9 k = kernel1_0_r3_9 k := by decide +kernel
lemma kernel1_0_r3_10_eq : ∀ k : Fin 16, kernel1_0Expr 3 10 k = kernel1_0_r3_10 k := by decide +kernel
lemma kernel1_0_r3_11_eq : ∀ k : Fin 16, kernel1_0Expr 3 11 k = kernel1_0_r3_11 k := by decide +kernel
lemma kernel1_0_r3_12_eq : ∀ k : Fin 16, kernel1_0Expr 3 12 k = kernel1_0_r3_12 k := by decide +kernel
lemma kernel1_0_r3_13_eq : ∀ k : Fin 16, kernel1_0Expr 3 13 k = kernel1_0_r3_13 k := by decide +kernel
lemma kernel1_0_r3_14_eq : ∀ k : Fin 16, kernel1_0Expr 3 14 k = kernel1_0_r3_14 k := by decide +kernel
lemma kernel1_0_r3_15_eq : ∀ k : Fin 16, kernel1_0Expr 3 15 k = kernel1_0_r3_15 k := by decide +kernel
lemma kernel1_0_r3_eq (i k : Fin 16) : kernel1_0Expr 3 i k = kernel1_0_r3 i k := by
  fin_cases i
  · exact kernel1_0_r3_0_eq k
  · exact kernel1_0_r3_1_eq k
  · exact kernel1_0_r3_2_eq k
  · exact kernel1_0_r3_3_eq k
  · exact kernel1_0_r3_4_eq k
  · exact kernel1_0_r3_5_eq k
  · exact kernel1_0_r3_6_eq k
  · exact kernel1_0_r3_7_eq k
  · exact kernel1_0_r3_8_eq k
  · exact kernel1_0_r3_9_eq k
  · exact kernel1_0_r3_10_eq k
  · exact kernel1_0_r3_11_eq k
  · exact kernel1_0_r3_12_eq k
  · exact kernel1_0_r3_13_eq k
  · exact kernel1_0_r3_14_eq k
  · exact kernel1_0_r3_15_eq k
lemma kernel1_0_r4_0_eq : ∀ k : Fin 16, kernel1_0Expr 4 0 k = kernel1_0_r4_0 k := by decide +kernel
lemma kernel1_0_r4_1_eq : ∀ k : Fin 16, kernel1_0Expr 4 1 k = kernel1_0_r4_1 k := by decide +kernel
lemma kernel1_0_r4_2_eq : ∀ k : Fin 16, kernel1_0Expr 4 2 k = kernel1_0_r4_2 k := by decide +kernel
lemma kernel1_0_r4_3_eq : ∀ k : Fin 16, kernel1_0Expr 4 3 k = kernel1_0_r4_3 k := by decide +kernel
lemma kernel1_0_r4_4_eq : ∀ k : Fin 16, kernel1_0Expr 4 4 k = kernel1_0_r4_4 k := by decide +kernel
lemma kernel1_0_r4_5_eq : ∀ k : Fin 16, kernel1_0Expr 4 5 k = kernel1_0_r4_5 k := by decide +kernel
lemma kernel1_0_r4_6_eq : ∀ k : Fin 16, kernel1_0Expr 4 6 k = kernel1_0_r4_6 k := by decide +kernel
lemma kernel1_0_r4_7_eq : ∀ k : Fin 16, kernel1_0Expr 4 7 k = kernel1_0_r4_7 k := by decide +kernel
lemma kernel1_0_r4_8_eq : ∀ k : Fin 16, kernel1_0Expr 4 8 k = kernel1_0_r4_8 k := by decide +kernel
lemma kernel1_0_r4_9_eq : ∀ k : Fin 16, kernel1_0Expr 4 9 k = kernel1_0_r4_9 k := by decide +kernel
lemma kernel1_0_r4_10_eq : ∀ k : Fin 16, kernel1_0Expr 4 10 k = kernel1_0_r4_10 k := by decide +kernel
lemma kernel1_0_r4_11_eq : ∀ k : Fin 16, kernel1_0Expr 4 11 k = kernel1_0_r4_11 k := by decide +kernel
lemma kernel1_0_r4_12_eq : ∀ k : Fin 16, kernel1_0Expr 4 12 k = kernel1_0_r4_12 k := by decide +kernel
lemma kernel1_0_r4_13_eq : ∀ k : Fin 16, kernel1_0Expr 4 13 k = kernel1_0_r4_13 k := by decide +kernel
lemma kernel1_0_r4_14_eq : ∀ k : Fin 16, kernel1_0Expr 4 14 k = kernel1_0_r4_14 k := by decide +kernel
lemma kernel1_0_r4_15_eq : ∀ k : Fin 16, kernel1_0Expr 4 15 k = kernel1_0_r4_15 k := by decide +kernel
lemma kernel1_0_r4_eq (i k : Fin 16) : kernel1_0Expr 4 i k = kernel1_0_r4 i k := by
  fin_cases i
  · exact kernel1_0_r4_0_eq k
  · exact kernel1_0_r4_1_eq k
  · exact kernel1_0_r4_2_eq k
  · exact kernel1_0_r4_3_eq k
  · exact kernel1_0_r4_4_eq k
  · exact kernel1_0_r4_5_eq k
  · exact kernel1_0_r4_6_eq k
  · exact kernel1_0_r4_7_eq k
  · exact kernel1_0_r4_8_eq k
  · exact kernel1_0_r4_9_eq k
  · exact kernel1_0_r4_10_eq k
  · exact kernel1_0_r4_11_eq k
  · exact kernel1_0_r4_12_eq k
  · exact kernel1_0_r4_13_eq k
  · exact kernel1_0_r4_14_eq k
  · exact kernel1_0_r4_15_eq k
lemma kernel1_0_r5_0_eq : ∀ k : Fin 16, kernel1_0Expr 5 0 k = kernel1_0_r5_0 k := by decide +kernel
lemma kernel1_0_r5_1_eq : ∀ k : Fin 16, kernel1_0Expr 5 1 k = kernel1_0_r5_1 k := by decide +kernel
lemma kernel1_0_r5_2_eq : ∀ k : Fin 16, kernel1_0Expr 5 2 k = kernel1_0_r5_2 k := by decide +kernel
lemma kernel1_0_r5_3_eq : ∀ k : Fin 16, kernel1_0Expr 5 3 k = kernel1_0_r5_3 k := by decide +kernel
lemma kernel1_0_r5_4_eq : ∀ k : Fin 16, kernel1_0Expr 5 4 k = kernel1_0_r5_4 k := by decide +kernel
lemma kernel1_0_r5_5_eq : ∀ k : Fin 16, kernel1_0Expr 5 5 k = kernel1_0_r5_5 k := by decide +kernel
lemma kernel1_0_r5_6_eq : ∀ k : Fin 16, kernel1_0Expr 5 6 k = kernel1_0_r5_6 k := by decide +kernel
lemma kernel1_0_r5_7_eq : ∀ k : Fin 16, kernel1_0Expr 5 7 k = kernel1_0_r5_7 k := by decide +kernel
lemma kernel1_0_r5_8_eq : ∀ k : Fin 16, kernel1_0Expr 5 8 k = kernel1_0_r5_8 k := by decide +kernel
lemma kernel1_0_r5_9_eq : ∀ k : Fin 16, kernel1_0Expr 5 9 k = kernel1_0_r5_9 k := by decide +kernel
lemma kernel1_0_r5_10_eq : ∀ k : Fin 16, kernel1_0Expr 5 10 k = kernel1_0_r5_10 k := by decide +kernel
lemma kernel1_0_r5_11_eq : ∀ k : Fin 16, kernel1_0Expr 5 11 k = kernel1_0_r5_11 k := by decide +kernel
lemma kernel1_0_r5_12_eq : ∀ k : Fin 16, kernel1_0Expr 5 12 k = kernel1_0_r5_12 k := by decide +kernel
lemma kernel1_0_r5_13_eq : ∀ k : Fin 16, kernel1_0Expr 5 13 k = kernel1_0_r5_13 k := by decide +kernel
lemma kernel1_0_r5_14_eq : ∀ k : Fin 16, kernel1_0Expr 5 14 k = kernel1_0_r5_14 k := by decide +kernel
lemma kernel1_0_r5_15_eq : ∀ k : Fin 16, kernel1_0Expr 5 15 k = kernel1_0_r5_15 k := by decide +kernel
lemma kernel1_0_r5_eq (i k : Fin 16) : kernel1_0Expr 5 i k = kernel1_0_r5 i k := by
  fin_cases i
  · exact kernel1_0_r5_0_eq k
  · exact kernel1_0_r5_1_eq k
  · exact kernel1_0_r5_2_eq k
  · exact kernel1_0_r5_3_eq k
  · exact kernel1_0_r5_4_eq k
  · exact kernel1_0_r5_5_eq k
  · exact kernel1_0_r5_6_eq k
  · exact kernel1_0_r5_7_eq k
  · exact kernel1_0_r5_8_eq k
  · exact kernel1_0_r5_9_eq k
  · exact kernel1_0_r5_10_eq k
  · exact kernel1_0_r5_11_eq k
  · exact kernel1_0_r5_12_eq k
  · exact kernel1_0_r5_13_eq k
  · exact kernel1_0_r5_14_eq k
  · exact kernel1_0_r5_15_eq k
lemma kernel1_0_eq (j : Fin 6) (i k : Fin 16) : kernel1_0Expr j i k = kernel1_0 j i k := by
  fin_cases j
  · exact kernel1_0_r0_eq i k
  · exact kernel1_0_r1_eq i k
  · exact kernel1_0_r2_eq i k
  · exact kernel1_0_r3_eq i k
  · exact kernel1_0_r4_eq i k
  · exact kernel1_0_r5_eq i k
lemma kernel1_0_contains (j : Fin 6) (i k : Fin 16) :
    (kernel1_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(1:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel1_0_eq]
  unfold kernel1_0Expr
  have hl := (gridRows_contains_e j i k).2.1
  rw [pointLambda_eq] at hl
  have hh := CBox.contains_mul_e hl (trans1_contains j i k)
  simpa only [Bool.false_eq_true,ite_false, if_false,mul_one] using hh
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DMoments1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm1_1_0_0
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox column1_0 kernel1_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 1 1 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column1_0_contains kernel1_0_contains
end cm1_1_0_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


lemma density_column (n : Node) (d : Bool) (j : ℕ) (t : ℝ) :
    density (positiveData (columnVector n d)) j t = basisFunction d n.val j t := by
  classical
  unfold density positiveData columnVector
  simp only [Complex.ofReal_zero, zero_mul, zero_add]
  rw [tsum_eq_single n]
  · cases d <;> simp [basisFunction,lp.single_apply]
  · intro k hk
    have hf : (k,false) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    have ht : (k,true) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    simp [Pi.single_eq_of_ne hf,Pi.single_eq_of_ne ht]

lemma K_column_integral (n : Node) (d e : Bool) (m : ℕ) :
    K (positiveData (columnVector n d)) (if e then 1 else 0) m =
      (∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n.val j.val m) j.val).re := by
  unfold K positiveData
  simp only [Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Finset.sum_range (fun j => pieceIntegral (complexBasisMoment d e n.val j m) j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold pieceIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [complexBasisMoment_ofReal,show density { C := 0, c₀ := 0, d₀ := 0, x := columnVector n d } j t = basisFunction d n.val j t from density_column n d j t]
  unfold kernelMoment basisMoment
  (cases e <;> simp); ring


lemma K_column_rule_error {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) :
    |K (positiveData (columnVector n d)) (if e then 1 else 0) m -
      (momentRuleValue quadraturePoint fejerWeight n.val m d e).re| < 1/10^22 := by
  rw [K_column_integral,← basis_rule_value]
  exact (Complex.abs_re_le_norm _).trans_lt (complexBasis_rule_error_e hn hm d e)

lemma S_column_derivative (n m : Node) (d : Bool) :
    S (columnVector n d) (m,true) =
      (D m.val * K (positiveData (columnVector n d)) 0 m.val -
        K (positiveData (columnVector n d)) 1 m.val) / Q m.val := by
  simp [S_apply,Scoords]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma dSmall_contains : dSmall.Contains (Real.pi*(3+2*b)/18) := by
  have hb := RBox.contains_add (RBox.contains_rat_e 3 1 (by norm_num))
    (RBox.contains_scale_e bBounds_contains_e 2 1 (by norm_num))
  convert RBox.contains_scale_e (RBox.contains_mul piBounds_contains_e hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dOther_contains : dOther.Contains (Real.pi*(3-2*b)/18) := by
  have hb := RBox.contains_add (RBox.contains_rat_e 3 1 (by norm_num))
    (RBox.contains_scale_e bBounds_contains_e (-2) 1 (by norm_num))
  convert RBox.contains_scale_e (RBox.contains_mul piBounds_contains_e hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dBase_contains : dBase.Contains (7*Real.pi*b/9) := by
  convert RBox.contains_scale_e (RBox.contains_mul piBounds_contains_e bBounds_contains_e) 7 9 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)

lemma dBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (dBox n).Contains (D n) := by
  have hh : D n = D (n%12) := by simp [D]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn
  · simpa [D_0_e,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_e dBase_contains
  · simpa [D_1_e,hn,dBox] using dSmall_contains
  · simpa [D_3_e,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_e dSmall_contains
  · simpa [D_4_e,hn,dBox] using dBase_contains
  · simpa [D_7_e,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_e dOther_contains
  · simpa [D_9_e,hn,dBox] using dOther_contains

lemma K_column_contains {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) {a : CBox}
    (ha : a.Contains (momentRuleValue quadraturePoint fejerWeight n.val m d e)) :
    (inflate a.re).Contains (K (positiveData (columnVector n d)) (if e then 1 else 0) m) :=
  inflate_contains_e ha.1 (K_column_rule_error hn hm d e)

lemma S_column_derivative_contains {n m : Node} {d : Bool} {a c : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val))
    (hc : c.Contains (K (positiveData (columnVector n d)) 1 m.val)) :
    (((dBox m.val).mul a).add c.neg |>.mul (qiBox m.val)).Contains (S (columnVector n d) (m,true)) := by
  rw [S_column_derivative,div_eq_mul_inv,sub_eq_add_neg]
  exact RBox.contains_mul
    (RBox.contains_add (RBox.contains_mul (dBox_contains m.val m.property.2) ha) (RBox.neg_contains_e hc))
    (qiBox_contains_e m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DEntries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma dentry3_0_contains_e_oai : dentry3_0.Contains (S (columnVector node1 false) (node1,true)) := by
  have h0 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) false false cm1_1_0_0.contains
  have h1 := K_column_contains (n:=node1) (m:=1) (by decide) (by decide) false true cm1_1_0_1.contains_e
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  decide +kernel
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.dentry3_0_contains_e_oai := @OAI.SharpPlanar.Numerical.dentry3_0_contains_e_oai
