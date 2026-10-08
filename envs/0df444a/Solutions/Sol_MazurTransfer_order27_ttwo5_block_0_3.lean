-- Prove2me | solution 1 for MazurTransfer.order27_ttwo5_block_0_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T16:29:19.850655+00:00
-- url     : https://prove2.me/submissions/4ec81d1e-5fa1-44ab-aee7-2994096799a0

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Theorems.Thm_MazurTransfer_order27_ttwo5_coefficients
namespace MazurTransfer.Order27TTwo5Polynomial
open Polynomial

lemma bridge_coeff_table_p_tlNSqP1c7 (f : ℚ) (n : ℕ) :
 (p_tlNSqP1c7 f).coeff n = c_tlNSqP1c7 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).1

lemma bridge_coeff_table_p_tlNSqP1c8 (f : ℚ) (n : ℕ) :
 (p_tlNSqP1c8 f).coeff n = c_tlNSqP1c8 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.1

lemma bridge_coeff_table_p_tlNSqP1c9 (f : ℚ) (n : ℕ) :
 (p_tlNSqP1c9 f).coeff n = c_tlNSqP1c9 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.1

lemma bridge_coeff_table_p_tlD0 (f : ℚ) (n : ℕ) :
 (p_tlD0 f).coeff n = c_tlD0 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.1

lemma bridge_coeff_table_p_tlD1 (f : ℚ) (n : ℕ) :
 (p_tlD1 f).coeff n = c_tlD1 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.1

lemma bridge_coeff_table_p_tlT0 (f : ℚ) (n : ℕ) :
 (p_tlT0 f).coeff n = c_tlT0 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.1

lemma bridge_coeff_table_p_tlT1 (f : ℚ) (n : ℕ) :
 (p_tlT1 f).coeff n = c_tlT1 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlT2 (f : ℚ) (n : ℕ) :
 (p_tlT2 f).coeff n = c_tlT2 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlT3 (f : ℚ) (n : ℕ) :
 (p_tlT3 f).coeff n = c_tlT3 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c0 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c0 f).coeff n = c_tlTTwoP5c0 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c1 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c1 f).coeff n = c_tlTTwoP5c1 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c2 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c2 f).coeff n = c_tlTTwoP5c2 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c3 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c3 f).coeff n = c_tlTTwoP5c3 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c4 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c4 f).coeff n = c_tlTTwoP5c4 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c5 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c5 f).coeff n = c_tlTTwoP5c5 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c6 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c6 f).coeff n = c_tlTTwoP5c6 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c7 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c7 f).coeff n = c_tlTTwoP5c7 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c8 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c8 f).coeff n = c_tlTTwoP5c8 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c9 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c9 f).coeff n = c_tlTTwoP5c9 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c10 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c10 f).coeff n = c_tlTTwoP5c10 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c11 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c11 f).coeff n = c_tlTTwoP5c11 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c12 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c12 f).coeff n = c_tlTTwoP5c12 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoP5c13 (f : ℚ) (n : ℕ) :
 (p_tlTTwoP5c13 f).coeff n = c_tlTTwoP5c13 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoQ5c0 (f : ℚ) (n : ℕ) :
 (p_tlTTwoQ5c0 f).coeff n = c_tlTTwoQ5c0 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoQ5c1 (f : ℚ) (n : ℕ) :
 (p_tlTTwoQ5c1 f).coeff n = c_tlTTwoQ5c1 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoQ5c2 (f : ℚ) (n : ℕ) :
 (p_tlTTwoQ5c2 f).coeff n = c_tlTTwoQ5c2 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoQ5c3 (f : ℚ) (n : ℕ) :
 (p_tlTTwoQ5c3 f).coeff n = c_tlTTwoQ5c3 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoQ5c4 (f : ℚ) (n : ℕ) :
 (p_tlTTwoQ5c4 f).coeff n = c_tlTTwoQ5c4 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoQ5c5 (f : ℚ) (n : ℕ) :
 (p_tlTTwoQ5c5 f).coeff n = c_tlTTwoQ5c5 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlTTwoQ5c6 (f : ℚ) (n : ℕ) :
 (p_tlTTwoQ5c6 f).coeff n = c_tlTTwoQ5c6 f n := by
 exact (MazurTransfer.order27_ttwo5_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

lemma fixed_tlNSqP1c7_0 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 0 = ((((-784418487) * f ^ 35) + (153753256 * f ^ 34)) + (((-24689552) * f ^ 33) + (3020658 * f ^ 32))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 0
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_1 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 1 = ((((-55317438366) * f ^ 35) + (15074726566 * f ^ 34)) + (((-3599133995) * f ^ 33) + ((734724249 * f ^ 32) + ((-123666520) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 1
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_2 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 2 = ((((-846365953634) * f ^ 35) + (294877862305 * f ^ 34)) + (((-93030865585) * f ^ 33) + ((26290285023 * f ^ 32) + ((-6541548424) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 2
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_3 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 3 = ((((-4578364031983) * f ^ 35) + (1931255914810 * f ^ 34)) + (((-746048179966) * f ^ 33) + ((263097930257 * f ^ 32) + ((-84320327757) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 3
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_4 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 4 = ((((-11123291134878) * f ^ 35) + (5607331787128 * f ^ 34)) + (((-2589035281836) * f ^ 33) + ((1094354097854 * f ^ 32) + ((-422720327857) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 4
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_5 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 5 = (((6684227203456 * f ^ 34) + ((-3863891235087) * f ^ 33)) + ((2018533799820 * f ^ 32) + ((-953433844909) * f ^ 31))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 5
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_6 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 6 = (((2578059258047 * f ^ 34) + ((-1960034210527) * f ^ 33)) + ((1343224015543 * f ^ 32) + ((-826076558476) * f ^ 31))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 6
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_7 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 7 = (((348423849890 * f ^ 34) + ((-343106429328) * f ^ 33)) + ((304692898427 * f ^ 32) + ((-243644480687) * f ^ 31))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 7
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_8 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 8 = (((13316282691 * f ^ 34) + ((-17773078080) * f ^ 33)) + ((21114503085 * f ^ 32) + ((-22340694824) * f ^ 31))) := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 8
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_9 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 9
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_10 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 10
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_11 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 11
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_12 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 12
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_13 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 13
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_14 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 14
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_15 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 15
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c7_16 (f : ℚ) :
 (p_tlNSqP1c7 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c7 f 16
 unfold c_tlNSqP1c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_0 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 0 = (((-239627) * f ^ 31) + (7799 * f ^ 30)) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 0
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_1 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 1 = ((16038926 * f ^ 30) + (((-1365674) * f ^ 29) + (46697 * f ^ 28))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 1
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_2 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 2 = (((1398693208 * f ^ 30) + ((-248400489) * f ^ 29)) + ((34505153 * f ^ 28) + (((-3211635) * f ^ 27) + (116500 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 2
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_3 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 3 = (((24359855203 * f ^ 30) + ((-6248467041) * f ^ 29)) + ((1388672726 * f ^ 28) + (((-258635620) * f ^ 27) + (38472955 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 3
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_4 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 4 = (((148728487863 * f ^ 30) + ((-47457350445) * f ^ 29)) + ((13663401347 * f ^ 28) + (((-3517888377) * f ^ 27) + (793401265 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 4
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_5 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 5 = (((407908035846 * f ^ 30) + ((-158323501732) * f ^ 29)) + ((55665390808 * f ^ 28) + (((-17610052881) * f ^ 27) + (4965380598 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 5
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_6 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 6 = (((453891833239 * f ^ 30) + ((-222107979931) * f ^ 29)) + ((96782714764 * f ^ 28) + (((-37712138436) * f ^ 27) + (13220347338 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 6
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_7 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 7 = (((174966018382 * f ^ 30) + ((-112369385552) * f ^ 29)) + ((64158682504 * f ^ 28) + (((-32318332212) * f ^ 27) + (14243936225 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 7
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_8 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 8 = (((21048088126 * f ^ 30) + ((-17636862949) * f ^ 29)) + ((13117460616 * f ^ 28) + (((-8635802389) * f ^ 27) + (5013191537 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 8
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_9 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 9
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_10 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 10
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_11 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 11
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_12 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 12
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_13 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 13
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_14 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 14
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_15 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 15
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c8_16 (f : ℚ) :
 (p_tlNSqP1c8 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c8 f 16
 unfold c_tlNSqP1c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_0 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 0
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_1 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 1
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_2 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 2 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 2
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_3 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 3 = (((-3990042) * f ^ 25) + (155010 * f ^ 24)) := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 3
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_4 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 4 = ((((-151065590) * f ^ 25) + (23462120 * f ^ 24)) + (((-2762748) * f ^ 23) + (116015 * f ^ 22))) := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 4
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_5 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 5 = ((((-1240751203) * f ^ 25) + ((273188692 * f ^ 24) + ((-50733467) * f ^ 23))) + ((7495718 * f ^ 22) + (((-1011399) * f ^ 21) + (46309 * f ^ 20)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 5
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_6 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 6 = (((((-4163567344) * f ^ 25) + (1155625080 * f ^ 24)) + (((-274621521) * f ^ 23) + (56349467 * f ^ 22))) + ((((-9902731) * f ^ 21) + (1060081 * f ^ 20)) + (((-153202) * f ^ 19) + (7702 * f ^ 18)))) := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 6
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_7 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 7 = (((((-5465760351) * f ^ 25) + (1836065828 * f ^ 24)) + (((-550124752) * f ^ 23) + (148313057 * f ^ 22))) + ((((-33361306) * f ^ 21) + (5720244 * f ^ 20)) + (((-1034291) * f ^ 19) + ((40413 * f ^ 18) + ((-97) * f ^ 17))))) := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 7
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_8 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 8 = (((((-2551576016) * f ^ 25) + (1126436206 * f ^ 24)) + (((-422561858) * f ^ 23) + (130500776 * f ^ 22))) + ((((-32044642) * f ^ 21) + (6676418 * f ^ 20)) + (((-1316742) * f ^ 19) + ((47875 * f ^ 18) + ((-11536) * f ^ 17))))) := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 8
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_9 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 9
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_10 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 10
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_11 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 11
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_12 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 12
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_13 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 13
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_14 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 14
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_15 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 15
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP1c9_16 (f : ℚ) :
 (p_tlNSqP1c9 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP1c9 f 16
 unfold c_tlNSqP1c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_0 (f : ℚ) :
 (p_tlD0 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 0
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_1 (f : ℚ) :
 (p_tlD0 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 1
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_2 (f : ℚ) :
 (p_tlD0 f).coeff 2 = ((((1 * f ^ 24) + (((-10) * f ^ 23) + (49 * f ^ 22))) + ((((-156) * f ^ 21) + (360 * f ^ 20)) + (((-636) * f ^ 19) + (886 * f ^ 18)))) + ((((-988) * f ^ 17) + ((886 * f ^ 16) + ((-636) * f ^ 15))) + (((360 * f ^ 14) + ((-156) * f ^ 13)) + ((49 * f ^ 12) + ((-10) * f ^ 11))))) := by
 have h := bridge_coeff_table_p_tlD0 f 2
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_3 (f : ℚ) :
 (p_tlD0 f).coeff 3 = (((((-2) * f ^ 21) + (16 * f ^ 20)) + (((-66) * f ^ 19) + ((186 * f ^ 18) + ((-396) * f ^ 17)))) + (((666 * f ^ 16) + (((-902) * f ^ 15) + (988 * f ^ 14))) + (((-870) * f ^ 13) + ((606 * f ^ 12) + ((-324) * f ^ 11))))) := by
 have h := bridge_coeff_table_p_tlD0 f 3
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_4 (f : ℚ) :
 (p_tlD0 f).coeff 4 = ((((1 * f ^ 18) + ((-4) * f ^ 17)) + ((9 * f ^ 16) + ((-18) * f ^ 15))) + (((38 * f ^ 14) + ((-80) * f ^ 13)) + ((143 * f ^ 12) + (((-200) * f ^ 11) + (213 * f ^ 10))))) := by
 have h := bridge_coeff_table_p_tlD0 f 4
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_5 (f : ℚ) :
 (p_tlD0 f).coeff 5 = ((((-2) * f ^ 14) + (8 * f ^ 13)) + (((-22) * f ^ 12) + ((46 * f ^ 11) + ((-70) * f ^ 10)))) := by
 have h := bridge_coeff_table_p_tlD0 f 5
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_6 (f : ℚ) :
 (p_tlD0 f).coeff 6 = (1 * f ^ 10) := by
 have h := bridge_coeff_table_p_tlD0 f 6
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_7 (f : ℚ) :
 (p_tlD0 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 7
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_8 (f : ℚ) :
 (p_tlD0 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 8
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_9 (f : ℚ) :
 (p_tlD0 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 9
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_10 (f : ℚ) :
 (p_tlD0 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 10
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_11 (f : ℚ) :
 (p_tlD0 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 11
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_12 (f : ℚ) :
 (p_tlD0 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 12
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_13 (f : ℚ) :
 (p_tlD0 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 13
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_14 (f : ℚ) :
 (p_tlD0 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 14
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_15 (f : ℚ) :
 (p_tlD0 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 15
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD0_16 (f : ℚ) :
 (p_tlD0 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlD0 f 16
 unfold c_tlD0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_0 (f : ℚ) :
 (p_tlD1 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 0
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_1 (f : ℚ) :
 (p_tlD1 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 1
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_2 (f : ℚ) :
 (p_tlD1 f).coeff 2 = (1 * f ^ 10) := by
 have h := bridge_coeff_table_p_tlD1 f 2
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_3 (f : ℚ) :
 (p_tlD1 f).coeff 3 = ((126 * f ^ 10) + (((-32) * f ^ 9) + (4 * f ^ 8))) := by
 have h := bridge_coeff_table_p_tlD1 f 3
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_4 (f : ℚ) :
 (p_tlD1 f).coeff 4 = ((((-168) * f ^ 9) + (94 * f ^ 8)) + (((-34) * f ^ 7) + (6 * f ^ 6))) := by
 have h := bridge_coeff_table_p_tlD1 f 4
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_5 (f : ℚ) :
 (p_tlD1 f).coeff 5 = (((78 * f ^ 9) + (((-58) * f ^ 8) + (22 * f ^ 7))) + ((4 * f ^ 6) + (((-10) * f ^ 5) + (4 * f ^ 4)))) := by
 have h := bridge_coeff_table_p_tlD1 f 5
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_6 (f : ℚ) :
 (p_tlD1 f).coeff 6 = ((((-3) * f ^ 8) + ((10 * f ^ 7) + ((-19) * f ^ 6))) + (((20 * f ^ 5) + ((-14) * f ^ 4)) + ((4 * f ^ 3) + (1 * f ^ 2)))) := by
 have h := bridge_coeff_table_p_tlD1 f 6
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_7 (f : ℚ) :
 (p_tlD1 f).coeff 7 = ((((-2) * f ^ 5) + (2 * f ^ 4)) + (((-2) * f ^ 3) + (2 * f))) := by
 have h := bridge_coeff_table_p_tlD1 f 7
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_8 (f : ℚ) :
 (p_tlD1 f).coeff 8 = 1 := by
 have h := bridge_coeff_table_p_tlD1 f 8
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_9 (f : ℚ) :
 (p_tlD1 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 9
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_10 (f : ℚ) :
 (p_tlD1 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 10
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_11 (f : ℚ) :
 (p_tlD1 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 11
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_12 (f : ℚ) :
 (p_tlD1 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 12
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_13 (f : ℚ) :
 (p_tlD1 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 13
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_14 (f : ℚ) :
 (p_tlD1 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 14
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_15 (f : ℚ) :
 (p_tlD1 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 15
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlD1_16 (f : ℚ) :
 (p_tlD1 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlD1 f 16
 unfold c_tlD1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_0 (f : ℚ) :
 (p_tlT0 f).coeff 0 = ((((1 * f ^ 33) + (((-13) * f ^ 32) + (84 * f ^ 31))) + (((-358) * f ^ 30) + ((1126 * f ^ 29) + ((-2772) * f ^ 28)))) + (((5531 * f ^ 27) + (((-9143) * f ^ 26) + (12696 * f ^ 25))) + (((-14932) * f ^ 24) + ((14932 * f ^ 23) + ((-12696) * f ^ 22))))) := by
 have h := bridge_coeff_table_p_tlT0 f 0
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_1 (f : ℚ) :
 (p_tlT0 f).coeff 1 = ((((3 * f ^ 31) + ((-39) * f ^ 30)) + ((249 * f ^ 29) + (((-1044) * f ^ 28) + (3231 * f ^ 27)))) + ((((-7851) * f ^ 26) + ((15543 * f ^ 25) + ((-25668) * f ^ 24))) + ((35898 * f ^ 23) + (((-42912) * f ^ 22) + (44046 * f ^ 21))))) := by
 have h := bridge_coeff_table_p_tlT0 f 1
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_2 (f : ℚ) :
 (p_tlT0 f).coeff 2 = ((((3 * f ^ 29) + ((-45) * f ^ 28)) + ((309 * f ^ 27) + ((-1341) * f ^ 26))) + (((4200 * f ^ 25) + ((-10182) * f ^ 24)) + ((19929 * f ^ 23) + (((-32373) * f ^ 22) + (44478 * f ^ 21))))) := by
 have h := bridge_coeff_table_p_tlT0 f 2
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_3 (f : ℚ) :
 (p_tlT0 f).coeff 3 = (((1 * f ^ 27) + (((-18) * f ^ 26) + (144 * f ^ 25))) + ((((-702) * f ^ 24) + (2426 * f ^ 23)) + (((-6435) * f ^ 22) + (13688 * f ^ 21)))) := by
 have h := bridge_coeff_table_p_tlT0 f 3
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_4 (f : ℚ) :
 (p_tlT0 f).coeff 4 = (12 * f ^ 21) := by
 have h := bridge_coeff_table_p_tlT0 f 4
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_5 (f : ℚ) :
 (p_tlT0 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 5
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_6 (f : ℚ) :
 (p_tlT0 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 6
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_7 (f : ℚ) :
 (p_tlT0 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 7
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_8 (f : ℚ) :
 (p_tlT0 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 8
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_9 (f : ℚ) :
 (p_tlT0 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 9
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_10 (f : ℚ) :
 (p_tlT0 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 10
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_11 (f : ℚ) :
 (p_tlT0 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 11
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_12 (f : ℚ) :
 (p_tlT0 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 12
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_13 (f : ℚ) :
 (p_tlT0 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 13
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_14 (f : ℚ) :
 (p_tlT0 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 14
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_15 (f : ℚ) :
 (p_tlT0 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 15
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT0_16 (f : ℚ) :
 (p_tlT0 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 16
 unfold c_tlT0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_0 (f : ℚ) :
 (p_tlT1 f).coeff 0 = ((((9143 * f ^ 21) + ((-5531) * f ^ 20)) + ((2772 * f ^ 19) + ((-1126) * f ^ 18))) + (((358 * f ^ 17) + ((-84) * f ^ 16)) + ((13 * f ^ 15) + ((-1) * f ^ 14)))) := by
 have h := bridge_coeff_table_p_tlT1 f 0
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_1 (f : ℚ) :
 (p_tlT1 f).coeff 1 = ((((-38838) * f ^ 20) + ((29313 * f ^ 19) + ((-18783) * f ^ 18))) + (((10077 * f ^ 17) + ((-4428) * f ^ 16)) + ((1539 * f ^ 15) + ((-399) * f ^ 14)))) := by
 have h := bridge_coeff_table_p_tlT1 f 1
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_2 (f : ℚ) :
 (p_tlT1 f).coeff 2 = ((((-52374) * f ^ 20) + ((53328 * f ^ 19) + ((-47184) * f ^ 18))) + (((36297 * f ^ 17) + ((-24159) * f ^ 16)) + ((13749 * f ^ 15) + ((-6549) * f ^ 14)))) := by
 have h := bridge_coeff_table_p_tlT1 f 2
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_3 (f : ℚ) :
 (p_tlT1 f).coeff 3 = ((((-23955) * f ^ 20) + ((35022 * f ^ 19) + ((-43163) * f ^ 18))) + (((45091 * f ^ 17) + ((-40068) * f ^ 16)) + ((30372 * f ^ 15) + ((-19699) * f ^ 14)))) := by
 have h := bridge_coeff_table_p_tlT1 f 3
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_4 (f : ℚ) :
 (p_tlT1 f).coeff 4 = ((((-144) * f ^ 20) + ((756 * f ^ 19) + ((-2487) * f ^ 18))) + (((5853 * f ^ 17) + ((-10476) * f ^ 16)) + ((14730 * f ^ 15) + ((-16539) * f ^ 14)))) := by
 have h := bridge_coeff_table_p_tlT1 f 4
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_5 (f : ℚ) :
 (p_tlT1 f).coeff 5 = (((-6) * f ^ 16) + ((90 * f ^ 15) + ((-426) * f ^ 14))) := by
 have h := bridge_coeff_table_p_tlT1 f 5
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_6 (f : ℚ) :
 (p_tlT1 f).coeff 6 = ((-1) * f ^ 14) := by
 have h := bridge_coeff_table_p_tlT1 f 6
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_7 (f : ℚ) :
 (p_tlT1 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 7
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_8 (f : ℚ) :
 (p_tlT1 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 8
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_9 (f : ℚ) :
 (p_tlT1 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 9
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_10 (f : ℚ) :
 (p_tlT1 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 10
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_11 (f : ℚ) :
 (p_tlT1 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 11
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_12 (f : ℚ) :
 (p_tlT1 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 12
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_13 (f : ℚ) :
 (p_tlT1 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 13
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_14 (f : ℚ) :
 (p_tlT1 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 14
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_15 (f : ℚ) :
 (p_tlT1 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 15
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT1_16 (f : ℚ) :
 (p_tlT1 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 16
 unfold c_tlT1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_0 (f : ℚ) :
 (p_tlT2 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 0
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_1 (f : ℚ) :
 (p_tlT2 f).coeff 1 = ((69 * f ^ 13) + ((-6) * f ^ 12)) := by
 have h := bridge_coeff_table_p_tlT2 f 1
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_2 (f : ℚ) :
 (p_tlT2 f).coeff 2 = (((2520 * f ^ 13) + ((-738) * f ^ 12)) + ((147 * f ^ 11) + ((-15) * f ^ 10))) := by
 have h := bridge_coeff_table_p_tlT2 f 2
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_3 (f : ℚ) :
 (p_tlT2 f).coeff 3 = (((10962 * f ^ 13) + (((-5227) * f ^ 12) + (2103 * f ^ 11))) + (((-681) * f ^ 10) + ((159 * f ^ 9) + ((-20) * f ^ 8)))) := by
 have h := bridge_coeff_table_p_tlT2 f 3
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_4 (f : ℚ) :
 (p_tlT2 f).coeff 4 = ((((14922 * f ^ 13) + ((-10818) * f ^ 12)) + ((6279 * f ^ 11) + ((-2916) * f ^ 10))) + (((1098 * f ^ 9) + ((-345) * f ^ 8)) + ((90 * f ^ 7) + ((-15) * f ^ 6)))) := by
 have h := bridge_coeff_table_p_tlT2 f 4
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_5 (f : ℚ) :
 (p_tlT2 f).coeff 5 = ((((1164 * f ^ 13) + ((-2166) * f ^ 12)) + ((2916 * f ^ 11) + ((-2916) * f ^ 10))) + (((2166 * f ^ 9) + ((-1170) * f ^ 8)) + ((444 * f ^ 7) + ((-114) * f ^ 6)))) := by
 have h := bridge_coeff_table_p_tlT2 f 5
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_6 (f : ℚ) :
 (p_tlT2 f).coeff 6 = ((((9 * f ^ 13) + ((-31) * f ^ 12)) + ((65 * f ^ 11) + ((-123) * f ^ 10))) + (((210 * f ^ 9) + ((-297) * f ^ 8)) + ((321 * f ^ 7) + ((-243) * f ^ 6)))) := by
 have h := bridge_coeff_table_p_tlT2 f 6
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_7 (f : ℚ) :
 (p_tlT2 f).coeff 7 = ((((-6) * f ^ 8) + (18 * f ^ 7)) + (((-24) * f ^ 6) + (24 * f ^ 5))) := by
 have h := bridge_coeff_table_p_tlT2 f 7
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_8 (f : ℚ) :
 (p_tlT2 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 8
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_9 (f : ℚ) :
 (p_tlT2 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 9
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_10 (f : ℚ) :
 (p_tlT2 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 10
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_11 (f : ℚ) :
 (p_tlT2 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 11
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_12 (f : ℚ) :
 (p_tlT2 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 12
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_13 (f : ℚ) :
 (p_tlT2 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 13
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_14 (f : ℚ) :
 (p_tlT2 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 14
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_15 (f : ℚ) :
 (p_tlT2 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 15
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT2_16 (f : ℚ) :
 (p_tlT2 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 16
 unfold c_tlT2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_0 (f : ℚ) :
 (p_tlT3 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 0
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_1 (f : ℚ) :
 (p_tlT3 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 1
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_2 (f : ℚ) :
 (p_tlT3 f).coeff 2 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 2
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_3 (f : ℚ) :
 (p_tlT3 f).coeff 3 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 3
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_4 (f : ℚ) :
 (p_tlT3 f).coeff 4 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 4
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_5 (f : ℚ) :
 (p_tlT3 f).coeff 5 = ((24 * f ^ 5) + ((-6) * f ^ 4)) := by
 have h := bridge_coeff_table_p_tlT3 f 5
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_6 (f : ℚ) :
 (p_tlT3 f).coeff 6 = (((122 * f ^ 5) + ((-33) * f ^ 4)) + ((2 * f ^ 3) + ((-1) * f ^ 2))) := by
 have h := bridge_coeff_table_p_tlT3 f 6
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_7 (f : ℚ) :
 (p_tlT3 f).coeff 7 = (((-18) * f ^ 4) + ((12 * f ^ 3) + ((-6) * f ^ 2))) := by
 have h := bridge_coeff_table_p_tlT3 f 7
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_8 (f : ℚ) :
 (p_tlT3 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 8
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_9 (f : ℚ) :
 (p_tlT3 f).coeff 9 = 1 := by
 have h := bridge_coeff_table_p_tlT3 f 9
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_10 (f : ℚ) :
 (p_tlT3 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 10
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_11 (f : ℚ) :
 (p_tlT3 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 11
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_12 (f : ℚ) :
 (p_tlT3 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 12
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_13 (f : ℚ) :
 (p_tlT3 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 13
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_14 (f : ℚ) :
 (p_tlT3 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 14
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_15 (f : ℚ) :
 (p_tlT3 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 15
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlT3_16 (f : ℚ) :
 (p_tlT3 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 16
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_0 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 0 = ((((26632565382 * f ^ 100) + (((-1087532488749) * f ^ 99) + (19929302549598 * f ^ 98))) + (((-226911660552172) * f ^ 97) + ((1861331283966061 * f ^ 96) + ((-12016227769544006) * f ^ 95)))) + (((64719807162905823 * f ^ 94) + (((-302414363626031489) * f ^ 93) + (1256891585754660710 * f ^ 92))) + (((-4715040554589397012) * f ^ 91) + ((16092998248721237258 * f ^ 90) + ((-50199935985364127822) * f ^ 89))))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 0
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_1 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 1 = ((((79897696146 * f ^ 98) + ((-3262597466247) * f ^ 97)) + ((59708009952648 * f ^ 96) + (((-677698760996016) * f ^ 95) + (5533709637916230 * f ^ 94)))) + ((((-35541555695650035) * f ^ 93) + (190514742941116576 * f ^ 92)) + (((-886675284513805035) * f ^ 91) + ((3673372330166397979 * f ^ 90) + ((-13742270824925580743) * f ^ 89))))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 1
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_2 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 2 = ((((79897696146 * f ^ 96) + ((-3422392858539) * f ^ 95)) + ((65753818708266 * f ^ 94) + ((-778391438196054) * f ^ 93))) + (((6565407130461213 * f ^ 92) + ((-43157411555208405) * f ^ 91)) + ((235114591299330882 * f ^ 90) + (((-1107174667030368030) * f ^ 89) + (4629419150513288642 * f ^ 88))))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 2
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_3 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 3 = (((26632565382 * f ^ 94) + (((-1220695315659) * f ^ 93) + (25233802166433 * f ^ 92))) + ((((-320787603789142) * f ^ 91) + (2886250972337484 * f ^ 90)) + (((-20064809222654177) * f ^ 89) + (114664675754384931 * f ^ 88)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 3
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_4 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 4 = ((13316282691 * f ^ 89) + (288501423813 * f ^ 88)) := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 4
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_5 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 5
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_6 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 6
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_7 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 7
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_8 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 8
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_9 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 9
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_10 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 10
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_11 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 11
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_12 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 12
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_13 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 13
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_14 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 14
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_15 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 15
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c0_16 (f : ℚ) :
 (p_tlTTwoP5c0 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c0 f 16
 unfold c_tlTTwoP5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_0 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 0 = (((143569363995193776909 * f ^ 88) + (((-377588348218913497555) * f ^ 87) + (916187159359725519355 * f ^ 86))) + ((((-2058139038672597895260) * f ^ 85) + (4295786156312802555243 * f ^ 84)) + (((-8359817081771863325514) * f ^ 83) + (15217265022675946053212 * f ^ 82)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 0
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_1 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 1 = (((46782792701990236074 * f ^ 88) + (((-145559478359197530984) * f ^ 87) + (415258874889854356650 * f ^ 86))) + ((((-1089668426876618193810) * f ^ 85) + (2639112515033714934165 * f ^ 84)) + (((-5921013133837716898876) * f ^ 83) + (12351251327112680747898 * f ^ 82)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 1
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_2 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 2 = ((((-17453243225943598749) * f ^ 87) + ((59802737575721910314 * f ^ 86) + ((-187032917387886903337) * f ^ 85))) + ((535569382369034451011 * f ^ 84) + (((-1408602627171412154163) * f ^ 83) + (3414956954105718420826 * f ^ 82)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 2
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_3 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 3 = ((((-562825828589355942) * f ^ 87) + ((2442444976301079023 * f ^ 86) + ((-9532504250374778110) * f ^ 85))) + (((33766800818195983885 * f ^ 84) + ((-109091041158258456823) * f ^ 83)) + ((322490641885663882933 * f ^ 82) + ((-874975514761016475018) * f ^ 81)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 3
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_4 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 4 = ((((-20069132110053) * f ^ 87) + ((386351432631517 * f ^ 86) + ((-4275129784711280) * f ^ 85))) + (((32989502358068567 * f ^ 84) + ((-196542158338872467) * f ^ 83)) + ((964319427335781630 * f ^ 82) + ((-4065189221624449925) * f ^ 81)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 4
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_5 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 5 = ((((-13316282691) * f ^ 85) + (377312710737 * f ^ 84)) + (((-4948626030039) * f ^ 83) + ((49833191667971 * f ^ 82) + ((-500384333482984) * f ^ 81)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 5
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_6 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 6 = ((-26632565382) * f ^ 81) := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 6
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_7 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 7
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_8 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 8
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_9 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 9
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_10 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 10
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_11 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 11
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_12 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 12
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_13 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 13
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_14 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 14
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_15 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 15
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c1_16 (f : ℚ) :
 (p_tlTTwoP5c1 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c1 f 16
 unfold c_tlTTwoP5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_0 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 0 = ((((-25984272286318123997727) * f ^ 81) + ((41725107603405960137812 * f ^ 80) + ((-63140344151294365624345) * f ^ 79))) + ((90196980064096773215470 * f ^ 78) + (((-121805541462262264374739) * f ^ 77) + (155677635656247015040334 * f ^ 76)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 0
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_1 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 1 = ((((-24040274694859720202182) * f ^ 81) + ((43801783064689330838469 * f ^ 80) + ((-74923289716677271654629) * f ^ 79))) + ((120611711714091573667443 * f ^ 78) + (((-183111385845664700678102) * f ^ 77) + (262630620621994212207107 * f ^ 76)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 1
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_2 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 2 = ((((-7661041028516454918573) * f ^ 81) + ((15966438881604930057398 * f ^ 80) + ((-31030494488401182900039) * f ^ 79))) + ((56432843031632842229559 * f ^ 78) + (((-96329952137527514341820) * f ^ 77) + (154743266563360879657771 * f ^ 76)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 2
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_3 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 3 = (((2186102516237135670202 * f ^ 80) + ((-5047911971101700505772) * f ^ 79)) + ((10812831756830550083012 * f ^ 78) + (((-21564280817694535298474) * f ^ 77) + (40176418233197989490522 * f ^ 76)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 3
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_4 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 4 = (((15129048535522247861 * f ^ 80) + ((-50534842245181368819) * f ^ 79)) + ((152989179370482700070 * f ^ 78) + (((-422335543365656316315) * f ^ 77) + (1067864579000376086888 * f ^ 76)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 4
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_5 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 5 = (((4546458591716314 * f ^ 80) + ((-33096983532758917) * f ^ 79)) + ((191290636910731664 * f ^ 78) + (((-906864868946463968) * f ^ 77) + (3648361681977679174 * f ^ 76)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 5
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_6 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 6 = (((1007634792603 * f ^ 80) + ((-16586807387205) * f ^ 79)) + ((163941053133277 * f ^ 78) + (((-1141408792190680) * f ^ 77) + (6278938223806532 * f ^ 76)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 6
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_7 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 7 = (((-13316282691) * f ^ 76) + ((-235236293049) * f ^ 75)) := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 7
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_8 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 8
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_9 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 9
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_10 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 10
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_11 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 11
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_12 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 12
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_13 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 13
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_14 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 14
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_15 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 15
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c2_16 (f : ℚ) :
 (p_tlTTwoP5c2 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c2 f 16
 unfold c_tlTTwoP5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_0 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 0 = ((((-188477354882679800767556) * f ^ 75) + (216303772793791790184591 * f ^ 74)) + (((-235428642143551609389295) * f ^ 73) + (243105498299845655088672 * f ^ 72))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 0
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_1 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 1 = ((((-356364239289707946240985) * f ^ 75) + (457991986287019854345236 * f ^ 74)) + (((-557994659821836946650706) * f ^ 73) + ((644932055279645736747970 * f ^ 72) + ((-707512343516143274212052) * f ^ 71)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 1
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_2 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 2 = ((((-234443730622273494123124) * f ^ 75) + (335612017988483591546210 * f ^ 74)) + (((-454638313157888004119564) * f ^ 73) + ((583530570178460294131540 * f ^ 72) + ((-710341855738830196313919) * f ^ 71)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 2
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_3 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 3 = ((((-70140235000686853845018) * f ^ 75) + (115044944488278567299782 * f ^ 74)) + (((-177681300559578311943859) * f ^ 73) + ((258879544801310857345304 * f ^ 72) + ((-356371074977559802844262) * f ^ 71)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 3
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_4 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 4 = ((((-2482863700572416794441) * f ^ 75) + (5329008222292160765889 * f ^ 74)) + (((-10598577461310724407556) * f ^ 73) + ((19602967048831439826204 * f ^ 72) + ((-33828728833732764244467) * f ^ 71)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 4
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_5 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 5 = ((((-12787464149150517898) * f ^ 75) + (39785318959294821492 * f ^ 74)) + (((-111309159585300043361) * f ^ 73) + ((282598944496729097086 * f ^ 72) + ((-655570083071222737076) * f ^ 71)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 5
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_6 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 6 = ((((-29677294071146775) * f ^ 75) + (125918900032913977 * f ^ 74)) + (((-484524597464260443) * f ^ 73) + ((1685092479506413345 * f ^ 72) + ((-5280257699858787779) * f ^ 71)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 6
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_7 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 7 = (((12168065575425 * f ^ 74) + ((-172356921472348) * f ^ 73)) + ((1388282935633515 * f ^ 72) + ((-7874294599206819) * f ^ 71))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 7
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_8 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 8 = ((13316282691 * f ^ 72) + ((-270782449209) * f ^ 71)) := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 8
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_9 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 9
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_10 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 10
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_11 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 11
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_12 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 12
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_13 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 13
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_14 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 14
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_15 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 15
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c3_16 (f : ℚ) :
 (p_tlTTwoP5c3 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c3 f 16
 unfold c_tlTTwoP5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_0 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 0 = ((((-238212287316734529391101) * f ^ 71) + (221521527470813501656633 * f ^ 70)) + (((-195506826137599922445809) * f ^ 69) + ((163749758569196643509825 * f ^ 68) + ((-130141331744365308022469) * f ^ 67)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 0
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_1 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 1 = (((736963462493499204947914 * f ^ 70) + ((-729032571566530161145966) * f ^ 69)) + ((684991016533877447902581 * f ^ 68) + ((-611316269961930655565148) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 1
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_2 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 2 = (((820776980385496867262204 * f ^ 70) + ((-900754250092775065773485) * f ^ 69)) + ((939316776112680034319338 * f ^ 68) + ((-931074779330779221099699) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 2
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_3 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 3 = (((464090862333820994689165 * f ^ 70) + ((-572328218131994711121313) * f ^ 69)) + ((668939951323081897933654 * f ^ 68) + ((-741499387840602113208043) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 3
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_4 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 4 = (((54622004825539484385573 * f ^ 70) + ((-82717932423058469852443) * f ^ 69)) + ((117715331060381179815595 * f ^ 68) + ((-157675619819190050805284) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 4
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_5 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 5 = (((1397312948056227612185 * f ^ 70) + ((-2749555322616381681896) * f ^ 69)) + ((5015520054248963031731 * f ^ 68) + ((-8510883872244460309737) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 5
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_6 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 6 = (((14923543745830030233 * f ^ 70) + ((-38210704301169494020) * f ^ 69)) + ((89154763625323411793 * f ^ 68) + (((-190709232933240240809) * f ^ 67) + (376077643996896807532 * f ^ 66)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 6
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_7 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 7 = (((35403075380500770 * f ^ 70) + ((-135047126634130740) * f ^ 69)) + ((452828463305663317 * f ^ 68) + (((-1357630943519905901) * f ^ 67) + (3668043207186167526 * f ^ 66)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 7
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_8 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 8 = (((2382877955637 * f ^ 70) + ((-16614418487582) * f ^ 69)) + ((130679460244959 * f ^ 68) + (((-923284635298369) * f ^ 67) + (4994752610067212 * f ^ 66)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 8
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_9 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 9
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_10 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 10
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_11 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 11
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_12 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 12
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_13 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 13
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_14 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 14
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_15 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 15
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c4_16 (f : ℚ) :
 (p_tlTTwoP5c4 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c4 f 16
 unfold c_tlTTwoP5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_0 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 0 = (((98122192892154194711651 * f ^ 66) + ((-70160242194501319576097) * f ^ 65)) + ((47554742586950260147070 * f ^ 64) + ((-30538263113431211719497) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 0
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_1 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 1 = (((518153973534050802042388 * f ^ 66) + ((-417056579888325048183743) * f ^ 65)) + ((318687883299383172479756 * f ^ 64) + ((-231109134912363859104310) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 1
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_2 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 2 = (((877433247147159501774872 * f ^ 66) + ((-786219589476139858472897) * f ^ 65)) + ((669841307927920134965692 * f ^ 64) + (((-542563957002418883455879) * f ^ 63) + (417721590692785634345137 * f ^ 62)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 2
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_3 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 3 = (((779887546114811561230295 * f ^ 66) + ((-778595325251488867154080) * f ^ 65)) + ((738020080339659281362525 * f ^ 64) + (((-664332413852993300120632) * f ^ 63) + (567961072601550634564246 * f ^ 62)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 3
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_4 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 4 = (((199049512688029391336004 * f ^ 66) + ((-237069607604036492563421) * f ^ 65)) + ((266598275664064912046145 * f ^ 64) + (((-283242070186188743024438) * f ^ 63) + (284411612177655468660272 * f ^ 62)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 4
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_5 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 5 = (((13473875605456096972689 * f ^ 66) + ((-19947269926948411270377) * f ^ 65)) + ((27667413667388221227183 * f ^ 64) + (((-36010138378778258276964) * f ^ 63) + (44036662871596429962256 * f ^ 62)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 5
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_6 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 6 = ((((-686980517096074012505) * f ^ 65) + (1167045828997174825943 * f ^ 64)) + (((-1849479200743207575064) * f ^ 63) + (2740432596922647434096 * f ^ 62))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 6
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_7 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 7 = ((((-8971614573725373064) * f ^ 65) + (19950925048662909331 * f ^ 64)) + (((-40529249566224321545) * f ^ 63) + (75586012640463369291 * f ^ 62))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 7
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_8 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 8 = ((((-21058532902468491) * f ^ 65) + (72590498466235411 * f ^ 64)) + (((-212768309357346067) * f ^ 63) + (546247659954229151 * f ^ 62))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 8
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_9 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 9
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_10 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 10
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_11 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 11
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_12 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 12
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_13 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 13
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_14 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 14
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_15 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 15
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c5_16 (f : ℚ) :
 (p_tlTTwoP5c5 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c5 f 16
 unfold c_tlTTwoP5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_0 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 0 = (((18569111973472274793093 * f ^ 62) + ((-10685234160266698205454) * f ^ 61)) + ((5815534123132639436210 * f ^ 60) + (((-2992202436906671074868) * f ^ 59) + (1454679792171002744793 * f ^ 58)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 0
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_1 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 1 = (((158982616515632461487880 * f ^ 62) + ((-103686115203235162063980) * f ^ 61)) + ((64070334516465454986394 * f ^ 60) + (((-37486392696774270567858) * f ^ 59) + (20753516473621868922698 * f ^ 58)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 1
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_2 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 2 = ((((-305589297617882764384743) * f ^ 61) + (212331826919782190984581 * f ^ 60)) + (((-140049854017147663270224) * f ^ 59) + (87632570928855156761768 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 2
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_3 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 3 = ((((-461202036869063995552365) * f ^ 61) + (355704437579219464837213 * f ^ 60)) + (((-260528282313626086097061) * f ^ 59) + (181169740798726777121479 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 3
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_4 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 4 = ((((-269982486570759622612073) * f ^ 61) + (242323353209846053989912 * f ^ 60)) + (((-205673689369864742764078) * f ^ 59) + (165089543520369727466845 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 4
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_5 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 5 = ((((-50651040045979137433017) * f ^ 61) + (54837088808806483482137 * f ^ 60)) + (((-55907619543140024435339) * f ^ 59) + (53686556760439756379583 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 5
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_6 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 6 = ((((-3802768058342740156807) * f ^ 61) + (4947684623861869665842 * f ^ 60)) + (((-6041398698307764089003) * f ^ 59) + (6929024327512022045618 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 6
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_7 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 7 = ((((-130036058410914547772) * f ^ 61) + (207245852482233283043 * f ^ 60)) + (((-307069512291279356062) * f ^ 59) + ((424110072971393685247 * f ^ 58) + ((-547036673849116038383) * f ^ 57)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 7
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_8 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 8 = ((((-1254361991219088847) * f ^ 61) + (2611190713940365353 * f ^ 60)) + (((-4967655899552590519) * f ^ 59) + ((8677325049795362608 * f ^ 58) + ((-13960309007517006344) * f ^ 57)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 8
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_9 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 9
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_10 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 10
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_11 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 11
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_12 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 12
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_13 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 13
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_14 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 14
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_15 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 15
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c6_16 (f : ℚ) :
 (p_tlTTwoP5c6 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c6 f 16
 unfold c_tlTTwoP5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_0 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 0 = ((((-667817554018812232999) * f ^ 57) + (289281569860219943373 * f ^ 56)) + (((-118114683957727382065) * f ^ 55) + (45396966313424008161 * f ^ 54))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 0
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_1 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 1 = ((((-10865447463551336960444) * f ^ 57) + (5376312411315875619827 * f ^ 56)) + (((-2512598009467012055865) * f ^ 55) + (1108204582838860920594 * f ^ 54))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 1
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_2 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 2 = ((((-51982635686447513966085) * f ^ 57) + (29210508374319695360592 * f ^ 56)) + (((-15537593450133304987039) * f ^ 55) + (7817556448747778181921 * f ^ 54))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 2
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_3 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 3 = ((((-119575295071586424063883) * f ^ 57) + (74878106367016990157021 * f ^ 56)) + (((-44467151842278244125013) * f ^ 55) + ((25031669313728195356364 * f ^ 54) + ((-13349854608806906354941) * f ^ 53)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 3
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_4 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 4 = ((((-125319628427724150715858) * f ^ 57) + (89955710228180298847621 * f ^ 56)) + (((-61044199901572762420939) * f ^ 55) + ((39149362808734081168949 * f ^ 54) + ((-23720746372631419714401) * f ^ 53)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 4
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_5 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 5 = ((((-48559786583320744320780) * f ^ 57) + (41371644926802211472811 * f ^ 56)) + (((-33200620692372988659736) * f ^ 55) + ((25095655996531277007820 * f ^ 54) + ((-17864647052744089732817) * f ^ 53)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 5
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_6 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 6 = ((((-7469928940287189213942) * f ^ 57) + (7573132618455633154610 * f ^ 56)) + (((-7221108247376538059633) * f ^ 55) + ((6474627412090508187611 * f ^ 54) + ((-5456970575425496329488) * f ^ 53)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 6
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_7 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 7 = (((659744018115575274315 * f ^ 56) + ((-744587472309701866744) * f ^ 55)) + ((786944962524895858401 * f ^ 54) + ((-779395932818326972123) * f ^ 53))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 7
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_8 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 8 = (((20745241705838765627 * f ^ 56) + ((-28557548542518609006) * f ^ 55)) + ((36517468074365202490 * f ^ 54) + ((-43465740788662528981) * f ^ 53))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 8
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_9 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 9
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_10 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 10
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_11 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 11
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_12 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 12
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_13 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 13
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_14 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 14
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_15 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 15
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c7_16 (f : ℚ) :
 (p_tlTTwoP5c7 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c7 f 16
 unfold c_tlTTwoP5c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_0 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 0 = ((((-16397088309034413264) * f ^ 53) + (5554330262649846773 * f ^ 52)) + (((-1760034560562425517) * f ^ 51) + ((520110264654780222 * f ^ 50) + ((-142816531452189271) * f ^ 49)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 0
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_1 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 1 = ((((-460817856524527456741) * f ^ 53) + (180417237780858248605 * f ^ 52)) + (((-66397716956133459146) * f ^ 51) + ((22923556444925737666 * f ^ 50) + ((-7406135631832145098) * f ^ 49)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 1
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_2 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 2 = ((((-3717670948518960111212) * f ^ 53) + (1669598958981121591363 * f ^ 52)) + (((-707355442043358562988) * f ^ 51) + ((282336950256032311446 * f ^ 50) + ((-105994133457636417794) * f ^ 49)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 2
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_3 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 3 = (((6741197753461149848194 * f ^ 52) + ((-3220847014361646529044) * f ^ 51)) + ((1454871817158621085494 * f ^ 50) + ((-620689464845606134289) * f ^ 49))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 3
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_4 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 4 = (((13575287555554739180829 * f ^ 52) + ((-7337039807418901508373) * f ^ 51)) + ((3744423797038581359012 * f ^ 50) + ((-1804003429308277579332) * f ^ 49))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 4
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_5 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 5 = (((11972186398054569243636 * f ^ 52) + ((-7549072256371635360092) * f ^ 51)) + ((4476171099562741898821 * f ^ 50) + ((-2494899147404139275052) * f ^ 49))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 5
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_6 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 6 = (((4321897440453733628298 * f ^ 52) + ((-3215848998187620336319) * f ^ 51)) + ((2247627331971080177071 * f ^ 50) + ((-1474894223439732585583) * f ^ 49))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 6
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_7 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 7 = (((723757489867017764854 * f ^ 52) + ((-630280084908694193192) * f ^ 51)) + ((514594440785686105002 * f ^ 50) + ((-393684642721408081417) * f ^ 49))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 7
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_8 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 8 = (((48207137410414957426 * f ^ 52) + ((-49834967656735873254) * f ^ 51)) + ((48028178282640435131 * f ^ 50) + (((-43174281464356808691) * f ^ 49) + (36225375688191966084 * f ^ 48)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 8
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_9 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 9
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_10 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 10
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_11 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 11
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_12 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 12
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_13 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 13
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_14 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 14
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_15 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 15
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c8_16 (f : ℚ) :
 (p_tlTTwoP5c8 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c8 f 16
 unfold c_tlTTwoP5c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_0 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 0 = (((36290048275560538 * f ^ 48) + ((-8494472439297346) * f ^ 47)) + ((1821977825621939 * f ^ 46) + ((-355787485137540) * f ^ 45))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 0
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_1 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 1 = (((2232348636100666004 * f ^ 48) + ((-625474730635379249) * f ^ 47)) + ((162224482538656395 * f ^ 46) + ((-38766424986180553) * f ^ 45))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 1
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_2 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 2 = (((37351627055475924869 * f ^ 48) + ((-12325347573313418096) * f ^ 47)) + ((3797138649092376818 * f ^ 46) + ((-1088166896770899387) * f ^ 45))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 2
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_3 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 3 = (((249790140193307150277 * f ^ 48) + ((-94673922941067035626) * f ^ 47)) + ((33727091346231891190 * f ^ 46) + ((-11266638097612884701) * f ^ 45))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 3
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_4 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 4 = (((820149905240818009848 * f ^ 48) + ((-351625469952803960568) * f ^ 47)) + ((142046465963344282527 * f ^ 46) + (((-54005187788592509165) * f ^ 45) + (19292624641497189489 * f ^ 44)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 4
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_5 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 5 = (((1307065294325192985639 * f ^ 48) + ((-643663756696629557075) * f ^ 47)) + ((297908487730800665661 * f ^ 46) + (((-129527418913922632175) * f ^ 45) + (52865315927649891023 * f ^ 44)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 5
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_6 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 6 = (((907917908933952750204 * f ^ 48) + ((-523781465002679765438) * f ^ 47)) + ((282981183105175058082 * f ^ 46) + (((-143147844969398713185) * f ^ 45) + (67804548150397910520 * f ^ 44)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 6
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_7 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 7 = (((282080257939132063490 * f ^ 48) + ((-189254299872585806720) * f ^ 47)) + ((118884051955247986870 * f ^ 46) + (((-69888484068603845718) * f ^ 45) + (38411591919406229165 * f ^ 44)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 7
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_8 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 8 = ((((-28373439805996467338) * f ^ 47) + (20728006956496452999 * f ^ 46)) + (((-14103303067931943207) * f ^ 45) + (8929493467920508997 * f ^ 44))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 8
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_9 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 9
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_10 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 10
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_11 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 11
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_12 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 12
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_13 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 13
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_14 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 14
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_15 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 15
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c9_16 (f : ℚ) :
 (p_tlTTwoP5c9 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c9 f 16
 unfold c_tlTTwoP5c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_0 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 0 = (((62714514172148 * f ^ 44) + ((-9864093516697) * f ^ 43)) + ((1361707678892 * f ^ 42) + (((-160388363530) * f ^ 41) + (15248349004 * f ^ 40)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 0
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_1 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 1 = (((8490677792525491 * f ^ 44) + ((-1693626008764081) * f ^ 43)) + ((305112920018654 * f ^ 42) + (((-49087524346083) * f ^ 41) + (6943923901132 * f ^ 40)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 1
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_2 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 2 = (((288835471687843743 * f ^ 44) + ((-70667874602444973) * f ^ 43)) + ((15851852846351600 * f ^ 42) + (((-3239736724342445) * f ^ 41) + (598407145483552 * f ^ 40)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 2
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_3 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 3 = (((3519148528343287051 * f ^ 44) + ((-1024169259360120414) * f ^ 43)) + ((276519447876848163 * f ^ 42) + (((-68916196201575516) * f ^ 41) + (15765845459869191 * f ^ 40)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 3
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_4 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 4 = ((((-6462449671214310812) * f ^ 43) + (2024764902873953972 * f ^ 42)) + (((-591562508982346761) * f ^ 41) + (160555895938151883 * f ^ 40))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 4
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_5 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 5 = ((((-20235705565749023903) * f ^ 43) + (7255357771793671940 * f ^ 42)) + (((-2432070531392331680) * f ^ 41) + (760392348773446578 * f ^ 40))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 5
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_6 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 6 = ((((-30063631967683649899) * f ^ 43) + (12464755864755844844 * f ^ 42)) + (((-4826464455253862851) * f ^ 41) + (1743203599895972805 * f ^ 40))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 6
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_7 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 7 = ((((-19717397528138916894) * f ^ 43) + (9448993607528449857 * f ^ 42)) + (((-4227812101478825397) * f ^ 41) + (1764850185404342382 * f ^ 40))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 7
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_8 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 8 = ((((-5263002093229934661) * f ^ 43) + (2889780321772984776 * f ^ 42)) + (((-1477833164578285199) * f ^ 41) + (702684196691386408 * f ^ 40))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 8
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_9 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 9
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_10 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 10
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_11 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 11
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_12 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 12
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_13 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 13
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_14 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 14
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_15 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 15
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c10_16 (f : ℚ) :
 (p_tlTTwoP5c10 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c10 f 16
 unfold c_tlTTwoP5c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_0 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 0 = ((((-1077269482) * f ^ 39) + (61849753 * f ^ 38)) + (((-4706952) * f ^ 37) + (116788 * f ^ 36))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 0
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_1 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 1 = ((((-841989329373) * f ^ 39) + (82903543910 * f ^ 38)) + (((-5989330809) * f ^ 37) + (330520273 * f ^ 36))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 1
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_2 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 2 = ((((-98791627766304) * f ^ 39) + (14363321029477 * f ^ 38)) + (((-1799335451664) * f ^ 37) + (184881169715 * f ^ 36))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 2
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_3 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 3 = ((((-3289843578194579) * f ^ 39) + (621295185691125 * f ^ 38)) + (((-105029586760264) * f ^ 37) + (15657923604836 * f ^ 36))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 3
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_4 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 4 = ((((-40292420763272543) * f ^ 39) + (9297089856534219 * f ^ 38)) + (((-1959777238959838) * f ^ 37) + (374619901553210 * f ^ 36))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 4
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_5 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 5 = ((((-221123189674545865) * f ^ 39) + (59617527953011753 * f ^ 38)) + (((-14847405380874809) * f ^ 37) + ((3399167214061863 * f ^ 36) + ((-710835300097851) * f ^ 35)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 5
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_6 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 6 = ((((-586185587307477887) * f ^ 39) + (183015744012582648 * f ^ 38)) + (((-52866289023250787) * f ^ 37) + ((14071237185691930 * f ^ 36) + ((-3437543800459542) * f ^ 35)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 6
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_7 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 7 = ((((-685863238202032772) * f ^ 39) + (247675486029444539 * f ^ 38)) + (((-82954420422323860) * f ^ 37) + ((25697437544618796 * f ^ 36) + ((-7333255511670643) * f ^ 35)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 7
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_8 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 8 = ((((-310322381778653502) * f ^ 39) + (127339272101647671 * f ^ 38)) + (((-48462097986700214) * f ^ 37) + ((17043270923681909 * f ^ 36) + ((-5520237114508073) * f ^ 35)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 8
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_9 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 9
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_10 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 10
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_11 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 11
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_12 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 12
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_13 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 13
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_14 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 14
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_15 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 15
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c11_16 (f : ℚ) :
 (p_tlTTwoP5c11 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c11 f 16
 unfold c_tlTTwoP5c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_0 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 0 = ((-97) * f ^ 35) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 0
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_1 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 1 = (((-27189177) * f ^ 35) + ((699855 * f ^ 34) + ((-582) * f ^ 33))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 1
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_2 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 2 = ((((-13811896655) * f ^ 35) + (716044418 * f ^ 34)) + (((-64992708) * f ^ 33) + ((1747164 * f ^ 32) + ((-1455) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 2
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_3 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 3 = ((((-2021191289660) * f ^ 35) + (217507466092 * f ^ 34)) + (((-17086815095) * f ^ 33) + ((804127089 * f ^ 32) + ((-82334805) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 3
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_4 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 4 = ((((-64273100689363) * f ^ 35) + ((9738927976140 * f ^ 34) + ((-1279590366826) * f ^ 33))) + ((143237633949 * f ^ 32) + (((-12133507783) * f ^ 31) + (493995368 * f ^ 30)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 4
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_5 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 5 = (((134812173451476 * f ^ 34) + ((-23008433072199) * f ^ 33)) + ((3479032540189 * f ^ 32) + (((-452472583291) * f ^ 31) + (50761502029 * f ^ 30)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 5
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_6 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 6 = (((767696262350000 * f ^ 34) + ((-155750410573456) * f ^ 33)) + ((28429439124483 * f ^ 32) + (((-4639880512895) * f ^ 31) + (675206912312 * f ^ 30)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 6
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_7 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 7 = (((1916360355851999 * f ^ 34) + ((-455300890396594) * f ^ 33)) + ((97718693524846 * f ^ 32) + (((-18823971085224) * f ^ 31) + (3201267942829 * f ^ 30)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 7
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_8 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 8 = (((1641397499414279 * f ^ 34) + ((-446853765604580) * f ^ 33)) + ((110939156826021 * f ^ 32) + (((-24877575909758) * f ^ 31) + (4957575559570 * f ^ 30)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 8
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_9 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 9
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_10 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 10
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_11 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 11
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_12 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 12
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_13 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 13
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_14 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 14
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_15 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 15
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c12_16 (f : ℚ) :
 (p_tlTTwoP5c12 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c12 f 16
 unfold c_tlTTwoP5c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_0 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 0
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_1 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 1
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_2 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 2 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 2
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_3 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 3 = ((2325963 * f ^ 30) + ((-1940) * f ^ 29)) := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 3
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_4 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 4 = (((-58333050) * f ^ 29) + ((1741635 * f ^ 28) + ((-1455) * f ^ 27))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 4
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_5 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 5 = ((((-4816342674) * f ^ 29) + (159422233 * f ^ 28)) + (((-21926319) * f ^ 27) + ((695490 * f ^ 26) + ((-582) * f ^ 25)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 5
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_6 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 6 = ((((-82782781001) * f ^ 29) + ((8058609180 * f ^ 28) + ((-913781408) * f ^ 27))) + (((23324339 * f ^ 26) + ((-3415566) * f ^ 25)) + ((115721 * f ^ 24) + ((-97) * f ^ 23)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 6
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_7 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 7 = ((((-467721738087) * f ^ 29) + ((60219488094 * f ^ 28) + ((-6701570755) * f ^ 27))) + (((257484868 * f ^ 26) + ((-44117074) * f ^ 25)) + ((1151791 * f ^ 24) + (2025 * f ^ 23)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 7
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_8 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 8 = (((((-867945174610) * f ^ 29) + (133066337826 * f ^ 28)) + (((-16388965449) * f ^ 27) + (1437784256 * f ^ 26))) + ((((-219676813) * f ^ 25) + (3300359 * f ^ 24)) + (((-149548) * f ^ 23) + (7508 * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 8
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_9 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 9
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_10 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 10
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_11 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 11
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_12 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 12
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_13 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 13
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_14 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 14
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_15 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 15
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoP5c13_16 (f : ℚ) :
 (p_tlTTwoP5c13 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoP5c13 f 16
 unfold c_tlTTwoP5c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_0 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 0 = ((((((-26632565382) * f ^ 67) + (741309138783 * f ^ 66)) + (((-8055148253331) * f ^ 65) + (50390307194341 * f ^ 64))) + ((((-234247896855378) * f ^ 63) + (945936669898388 * f ^ 62)) + (((-3433766557715925) * f ^ 61) + (11043931779076651 * f ^ 60)))) + (((((-31124749057878161) * f ^ 59) + (76813911479169985 * f ^ 58)) + (((-167574544838520148) * f ^ 57) + (327423683138657856 * f ^ 56))) + ((((-579731902441855216) * f ^ 55) + (938351149778933158 * f ^ 54)) + (((-1395486905723199999) * f ^ 53) + ((1912306447367611471 * f ^ 52) + ((-2420560835236732142) * f ^ 51)))))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 0
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_1 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 1 = (((((-13316282691) * f ^ 62) + (((-208603727667) * f ^ 61) + (5461061791074 * f ^ 60))) + (((-42804808015711) * f ^ 59) + ((200856494944787 * f ^ 58) + ((-704809242665351) * f ^ 57)))) + (((2028157384285079 * f ^ 56) + (((-5024428917670336) * f ^ 55) + (11057580057053872 * f ^ 54))) + (((-21909269773141418) * f ^ 53) + ((39364426594129306 * f ^ 52) + ((-64400655629212042) * f ^ 51))))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 1
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_2 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 2 = ((((13316282691 * f ^ 58) + ((-137619622299) * f ^ 57)) + ((553928121153 * f ^ 56) + ((-3186845989355) * f ^ 55))) + (((20058703331929 * f ^ 54) + ((-87613173309757) * f ^ 53)) + ((284747155573036 * f ^ 52) + ((-729569749624618) * f ^ 51)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 2
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_3 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 3 = (((-26632565382) * f ^ 53) + ((395085788817 * f ^ 52) + ((-1906995514194) * f ^ 51))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 3
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_4 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 4 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 4
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_5 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 5
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_6 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 6
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_7 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 7
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_8 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 8
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_9 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 9
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_10 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 10
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_11 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 11
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_12 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 12
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_13 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 13
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_14 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 14
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_15 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 15
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c0_16 (f : ℚ) :
 (p_tlTTwoQ5c0 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c0 f 16
 unfold c_tlTTwoQ5c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_0 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 0 = ((((2836447609209171396 * f ^ 50) + ((-3082672414694330067) * f ^ 49)) + ((3108629288282102733 * f ^ 48) + ((-2906599581481267950) * f ^ 47))) + (((2518801635143712991 * f ^ 46) + ((-2024359046992859302) * f ^ 45)) + ((1511250056053602447 * f ^ 44) + ((-1048004121089975231) * f ^ 43)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 0
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_1 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 1 = ((((96039957549213975 * f ^ 50) + ((-130788332393668182) * f ^ 49)) + ((162903640635852582 * f ^ 48) + ((-186277637698669409) * f ^ 47))) + (((196632992685421399 * f ^ 46) + ((-192089530254720237) * f ^ 45)) + ((173481498674849008 * f ^ 44) + ((-144153187725757426) * f ^ 43)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 1
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_2 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 2 = ((((1539092592527559 * f ^ 50) + ((-2803648088001514) * f ^ 49)) + ((4543129988738277 * f ^ 48) + ((-6715254445275810) * f ^ 47))) + (((9145572888818840 * f ^ 46) + ((-11366581671138224) * f ^ 45)) + ((12808180980049838 * f ^ 44) + ((-13025021506990921) * f ^ 43)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 2
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_3 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 3 = ((((6018620571760 * f ^ 50) + ((-16508524507670) * f ^ 49)) + ((40178436887047 * f ^ 48) + ((-91467485759551) * f ^ 47))) + (((186241395164338 * f ^ 46) + ((-321700328916886) * f ^ 45)) + ((481912945488446 * f ^ 44) + ((-630724137245188) * f ^ 43)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 3
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_4 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 4 = ((((-13316282691) * f ^ 48) + (((-155338596903) * f ^ 47) + (968963625342 * f ^ 46))) + (((-2796585805306) * f ^ 45) + ((6328747747356 * f ^ 44) + ((-10944404854692) * f ^ 43)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 4
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_5 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 5 = ((13316282691 * f ^ 44) + ((-17773078080) * f ^ 43)) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 5
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_6 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 6
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_7 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 7
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_8 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 8
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_9 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 9
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_10 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 10
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_11 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 11
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_12 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 12
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_13 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 13
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_14 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 14
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_15 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 15
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c1_16 (f : ℚ) :
 (p_tlTTwoQ5c1 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c1 f 16
 unfold c_tlTTwoQ5c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_0 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 0 = (((673291974462530271 * f ^ 42) + (((-399508688477718570) * f ^ 41) + (218786328267339510 * f ^ 40))) + (((-110956546480689779) * f ^ 39) + ((52213443170067629 * f ^ 38) + ((-22720306729119049) * f ^ 37)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 0
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_1 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 1 = (((109930349231010757 * f ^ 42) + (((-77225595046761716) * f ^ 41) + (50169184368314442 * f ^ 40))) + (((-30150487383650858) * f ^ 39) + ((16627055279661110 * f ^ 38) + ((-8376897595642841) * f ^ 37)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 1
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_2 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 2 = (((12090089184560935 * f ^ 42) + (((-10388563521484579) * f ^ 41) + (8206854283031987 * f ^ 40))) + (((-5899857246611528) * f ^ 39) + ((3821261783877509 * f ^ 38) + ((-2263869980824243) * f ^ 37)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 2
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_3 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 3 = (((754808870682902 * f ^ 42) + (((-835419158363659) * f ^ 41) + (820138988411299 * f ^ 40))) + (((-730126957628436) * f ^ 39) + ((581780765139343 * f ^ 38) + ((-436482850647101) * f ^ 37)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 3
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_4 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 4 = (((17861409797546 * f ^ 42) + (((-26930546987926) * f ^ 41) + (33419594642122 * f ^ 40))) + (((-41559271017765) * f ^ 39) + ((44902630218691 * f ^ 38) + ((-45679915250204) * f ^ 37)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 4
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_5 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 5 = (((61063351158 * f ^ 42) + (((-182190190592) * f ^ 41) + (293157635476 * f ^ 40))) + (((-1092553193045) * f ^ 39) + ((1867977800531 * f ^ 38) + ((-2596161511842) * f ^ 37)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 5
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_6 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 6 = ((((-26632565382) * f ^ 39) + (62178721542 * f ^ 38)) + (((-104407727712) * f ^ 37) + (122456551978 * f ^ 36))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 6
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_7 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 7
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_8 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 8
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_9 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 9
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_10 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 10
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_11 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 11
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_12 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 12
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_13 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 13
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_14 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 14
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_15 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 15
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c2_16 (f : ℚ) :
 (p_tlTTwoQ5c2 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c2 f 16
 unfold c_tlTTwoQ5c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_0 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 0 = (((9130242990524028 * f ^ 36) + ((-3388017903468048) * f ^ 35)) + ((1157820466111986 * f ^ 34) + (((-362809679449008) * f ^ 33) + (103499444801318 * f ^ 32)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 0
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_1 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 1 = (((3890121609395694 * f ^ 36) + ((-1666794293110832) * f ^ 35)) + ((654994227886299 * f ^ 34) + (((-235362475236919) * f ^ 33) + (77180366546857 * f ^ 32)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 1
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_2 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 2 = (((1246626177223623 * f ^ 36) + ((-626814755134129) * f ^ 35)) + ((287482526807953 * f ^ 34) + (((-121040526823953) * f ^ 33) + (46652706292821 * f ^ 32)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 2
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_3 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 3 = (((298718569581296 * f ^ 36) + ((-176571351407653) * f ^ 35)) + ((95836025393181 * f ^ 34) + (((-47458117955452) * f ^ 33) + (21352821160537 * f ^ 32)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 3
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_4 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 4 = (((38328412951499 * f ^ 36) + ((-23109777830027) * f ^ 35)) + ((21938582019995 * f ^ 34) + (((-13105845426062) * f ^ 33) + (7144978715846 * f ^ 32)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 4
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_5 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 5 = (((2482807929604 * f ^ 36) + (((-1438224781108) * f ^ 35) + (3585912786129 * f ^ 34))) + (((-2592785283732) * f ^ 33) + ((1698060802406 * f ^ 32) + ((-1003649224813) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 5
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_6 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 6 = ((((-102374006688) * f ^ 35) + (434928985528 * f ^ 34)) + (((-404482246540) * f ^ 33) + ((338791760687 * f ^ 32) + ((-255081213519) * f ^ 31)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 6
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_7 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 7 = (((13316282691 * f ^ 34) + ((-17773078080) * f ^ 33)) + ((21114503085 * f ^ 32) + ((-22340694824) * f ^ 31))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 7
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_8 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 8
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_9 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 9
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_10 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 10
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_11 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 11
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_12 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 12
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_13 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 13
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_14 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 14
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_15 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 15
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c3_16 (f : ℚ) :
 (p_tlTTwoQ5c3 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c3 f 16
 unfold c_tlTTwoQ5c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_0 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 0 = ((((-26653111994947) * f ^ 31) + (6163753162867 * f ^ 30)) + (((-1278267159910) * f ^ 29) + ((233994627383 * f ^ 28) + ((-36115182829) * f ^ 27)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 0
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_1 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 1 = ((((-23095939998870) * f ^ 31) + (6298129983196 * f ^ 30)) + (((-1548003024634) * f ^ 29) + ((334740801668 * f ^ 28) + ((-62608319129) * f ^ 27)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 1
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_2 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 2 = ((((-16364175828008) * f ^ 31) + (5172778601941 * f ^ 30)) + (((-1458306279328) * f ^ 29) + ((365919983538 * f ^ 28) + ((-82631679191) * f ^ 27)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 2
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_3 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 3 = ((((-8704189040384) * f ^ 31) + (3216543092293 * f ^ 30)) + (((-1082485006176) * f ^ 29) + ((332507313476 * f ^ 28) + ((-91862539313) * f ^ 27)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 3
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_4 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 4 = ((((-3545572153595) * f ^ 31) + (1593163947921 * f ^ 30)) + (((-641943892351) * f ^ 29) + ((228647050349 * f ^ 28) + ((-71086103334) * f ^ 27)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 4
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_5 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 5 = (((533787687987 * f ^ 30) + ((-255404603804) * f ^ 29)) + ((110479831490 * f ^ 28) + (((-43595641872) * f ^ 27) + (15712214495 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 5
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_6 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 6 = (((172093432368 * f ^ 30) + ((-103516871838) * f ^ 29)) + ((55088225886 * f ^ 28) + (((-25650946818) * f ^ 27) + (10310998745 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 6
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_7 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 7 = (((21048088126 * f ^ 30) + ((-17636862949) * f ^ 29)) + ((13117460616 * f ^ 28) + (((-8635802389) * f ^ 27) + (5013191537 * f ^ 26)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 7
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_8 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 8
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_9 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 9
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_10 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 10
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_11 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 11
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_12 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 12
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_13 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 13
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_14 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 14
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_15 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 15
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c4_16 (f : ℚ) :
 (p_tlTTwoQ5c4 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c4 f 16
 unfold c_tlTTwoQ5c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_0 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 0 = (((4895920948 * f ^ 26) + ((-630102732) * f ^ 25)) + ((10550370 * f ^ 24) + (((-3196953) * f ^ 23) + (115527 * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 0
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_1 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 1 = (((10298772035 * f ^ 26) + ((-1340053397) * f ^ 25)) + ((92197566 * f ^ 24) + (((-21718856) * f ^ 23) + (417631 * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 1
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_2 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 2 = (((16671356807 * f ^ 26) + ((-2773505149) * f ^ 25)) + ((395276640 * f ^ 24) + (((-64678706) * f ^ 23) + ((-145129) * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 2
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_3 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 3 = (((21939955333 * f ^ 26) + ((-4384104962) * f ^ 25)) + ((775074844 * f ^ 24) + (((-110764279) * f ^ 23) + (3217715 * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 3
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_4 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 4 = (((19407357542 * f ^ 26) + ((-4846997850) * f ^ 25)) + ((1132513185 * f ^ 24) + (((-214346466) * f ^ 23) + (31867401 * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 4
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_5 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 5 = ((((-5030049674) * f ^ 25) + (1337774129 * f ^ 24)) + (((-274825289) * f ^ 23) + ((49282963 * f ^ 22) + ((-8189601) * f ^ 21)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 5
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_6 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 6 = ((((-3551331611) * f ^ 25) + (1071017716 * f ^ 24)) + (((-305205270) * f ^ 23) + ((86976079 * f ^ 22) + ((-20127292) * f ^ 21)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 6
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_7 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 7 = ((((-2551576016) * f ^ 25) + (1126436206 * f ^ 24)) + (((-422561858) * f ^ 23) + ((130500776 * f ^ 22) + ((-32044642) * f ^ 21)))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 7
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_8 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 8
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_9 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 9
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_10 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 10
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_11 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 11
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_12 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 12
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_13 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 13
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_14 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 14
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_15 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 15
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c5_16 (f : ℚ) :
 (p_tlTTwoQ5c5 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c5 f 16
 unfold c_tlTTwoQ5c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_0 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 0 = ((-97) * f ^ 21) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 0
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_1 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 1 = (2607 * f ^ 21) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 1
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_2 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 2 = (((-149592) * f ^ 21) + (7508 * f ^ 20)) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 2
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_3 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 3 = (((-2084668) * f ^ 21) + ((70285 * f ^ 20) + ((-97) * f ^ 19))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 3
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_4 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 4 = (((-7458330) * f ^ 21) + (((-43913) * f ^ 20) + (3189 * f ^ 19))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 4
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_5 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 5 = (((-580894) * f ^ 20) + (((-153128) * f ^ 19) + (7508 * f ^ 18))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 5
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_6 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 6 = (((3109832 * f ^ 20) + ((-938541) * f ^ 19)) + ((17341 * f ^ 18) + ((-97) * f ^ 17))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 6
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_7 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 7 = (((6676418 * f ^ 20) + ((-1316742) * f ^ 19)) + ((47875 * f ^ 18) + ((-11536) * f ^ 17))) := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 7
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_8 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 8
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_9 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 9
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_10 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 10
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_11 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 11
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_12 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 12
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_13 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 13
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_14 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 14
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_15 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 15
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlTTwoQ5c6_16 (f : ℚ) :
 (p_tlTTwoQ5c6 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlTTwoQ5c6 f 16
 unfold c_tlTTwoQ5c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

end MazurTransfer.Order27TTwo5Polynomial
open Polynomial MazurTransfer.Order27TTwo5Polynomial

lemma coefficient_0 (f : ℚ) : (leftSide f).coeff 0 = (rightSide f).coeff 0 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP1c7_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c8_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c9_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD0_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD1_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c0_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c1_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c2_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c3_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c4_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c5_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c6_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c7_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c8_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c9_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c10_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c11_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c12_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c13_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c0_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c1_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c2_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c3_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c4_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c5_0, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c6_0, add_zero, zero_add, mul_zero, zero_mul]
 try ring

lemma coefficient_1 (f : ℚ) : (leftSide f).coeff 1 = (rightSide f).coeff 1 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP1c7_0, fixed_tlNSqP1c7_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c8_0, fixed_tlNSqP1c8_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c9_0, fixed_tlNSqP1c9_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD0_0, fixed_tlD0_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD1_0, fixed_tlD1_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, fixed_tlT0_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, fixed_tlT1_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, fixed_tlT2_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, fixed_tlT3_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c0_0, fixed_tlTTwoP5c0_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c1_0, fixed_tlTTwoP5c1_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c2_0, fixed_tlTTwoP5c2_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c3_0, fixed_tlTTwoP5c3_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c4_0, fixed_tlTTwoP5c4_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c5_0, fixed_tlTTwoP5c5_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c6_0, fixed_tlTTwoP5c6_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c7_0, fixed_tlTTwoP5c7_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c8_0, fixed_tlTTwoP5c8_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c9_0, fixed_tlTTwoP5c9_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c10_0, fixed_tlTTwoP5c10_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c11_0, fixed_tlTTwoP5c11_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c12_0, fixed_tlTTwoP5c12_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c13_0, fixed_tlTTwoP5c13_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c0_0, fixed_tlTTwoQ5c0_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c1_0, fixed_tlTTwoQ5c1_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c2_0, fixed_tlTTwoQ5c2_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c3_0, fixed_tlTTwoQ5c3_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c4_0, fixed_tlTTwoQ5c4_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c5_0, fixed_tlTTwoQ5c5_1, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c6_0, fixed_tlTTwoQ5c6_1, add_zero, zero_add, mul_zero, zero_mul]
 try ring

lemma coefficient_2 (f : ℚ) : (leftSide f).coeff 2 = (rightSide f).coeff 2 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP1c7_0, fixed_tlNSqP1c7_1, fixed_tlNSqP1c7_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c8_0, fixed_tlNSqP1c8_1, fixed_tlNSqP1c8_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c9_0, fixed_tlNSqP1c9_1, fixed_tlNSqP1c9_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD0_0, fixed_tlD0_1, fixed_tlD0_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD1_0, fixed_tlD1_1, fixed_tlD1_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, fixed_tlT0_1, fixed_tlT0_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, fixed_tlT1_1, fixed_tlT1_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, fixed_tlT2_1, fixed_tlT2_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, fixed_tlT3_1, fixed_tlT3_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c0_0, fixed_tlTTwoP5c0_1, fixed_tlTTwoP5c0_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c1_0, fixed_tlTTwoP5c1_1, fixed_tlTTwoP5c1_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c2_0, fixed_tlTTwoP5c2_1, fixed_tlTTwoP5c2_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c3_0, fixed_tlTTwoP5c3_1, fixed_tlTTwoP5c3_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c4_0, fixed_tlTTwoP5c4_1, fixed_tlTTwoP5c4_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c5_0, fixed_tlTTwoP5c5_1, fixed_tlTTwoP5c5_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c6_0, fixed_tlTTwoP5c6_1, fixed_tlTTwoP5c6_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c7_0, fixed_tlTTwoP5c7_1, fixed_tlTTwoP5c7_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c8_0, fixed_tlTTwoP5c8_1, fixed_tlTTwoP5c8_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c9_0, fixed_tlTTwoP5c9_1, fixed_tlTTwoP5c9_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c10_0, fixed_tlTTwoP5c10_1, fixed_tlTTwoP5c10_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c11_0, fixed_tlTTwoP5c11_1, fixed_tlTTwoP5c11_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c12_0, fixed_tlTTwoP5c12_1, fixed_tlTTwoP5c12_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c13_0, fixed_tlTTwoP5c13_1, fixed_tlTTwoP5c13_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c0_0, fixed_tlTTwoQ5c0_1, fixed_tlTTwoQ5c0_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c1_0, fixed_tlTTwoQ5c1_1, fixed_tlTTwoQ5c1_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c2_0, fixed_tlTTwoQ5c2_1, fixed_tlTTwoQ5c2_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c3_0, fixed_tlTTwoQ5c3_1, fixed_tlTTwoQ5c3_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c4_0, fixed_tlTTwoQ5c4_1, fixed_tlTTwoQ5c4_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c5_0, fixed_tlTTwoQ5c5_1, fixed_tlTTwoQ5c5_2, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c6_0, fixed_tlTTwoQ5c6_1, fixed_tlTTwoQ5c6_2, add_zero, zero_add, mul_zero, zero_mul]
 try ring

lemma coefficient_3 (f : ℚ) : (leftSide f).coeff 3 = (rightSide f).coeff 3 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP1c7_0, fixed_tlNSqP1c7_1, fixed_tlNSqP1c7_2, fixed_tlNSqP1c7_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c8_0, fixed_tlNSqP1c8_1, fixed_tlNSqP1c8_2, fixed_tlNSqP1c8_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNSqP1c9_0, fixed_tlNSqP1c9_1, fixed_tlNSqP1c9_2, fixed_tlNSqP1c9_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD0_0, fixed_tlD0_1, fixed_tlD0_2, fixed_tlD0_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlD1_0, fixed_tlD1_1, fixed_tlD1_2, fixed_tlD1_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, fixed_tlT0_1, fixed_tlT0_2, fixed_tlT0_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, fixed_tlT1_1, fixed_tlT1_2, fixed_tlT1_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, fixed_tlT2_1, fixed_tlT2_2, fixed_tlT2_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, fixed_tlT3_1, fixed_tlT3_2, fixed_tlT3_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c0_0, fixed_tlTTwoP5c0_1, fixed_tlTTwoP5c0_2, fixed_tlTTwoP5c0_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c1_0, fixed_tlTTwoP5c1_1, fixed_tlTTwoP5c1_2, fixed_tlTTwoP5c1_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c2_0, fixed_tlTTwoP5c2_1, fixed_tlTTwoP5c2_2, fixed_tlTTwoP5c2_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c3_0, fixed_tlTTwoP5c3_1, fixed_tlTTwoP5c3_2, fixed_tlTTwoP5c3_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c4_0, fixed_tlTTwoP5c4_1, fixed_tlTTwoP5c4_2, fixed_tlTTwoP5c4_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c5_0, fixed_tlTTwoP5c5_1, fixed_tlTTwoP5c5_2, fixed_tlTTwoP5c5_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c6_0, fixed_tlTTwoP5c6_1, fixed_tlTTwoP5c6_2, fixed_tlTTwoP5c6_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c7_0, fixed_tlTTwoP5c7_1, fixed_tlTTwoP5c7_2, fixed_tlTTwoP5c7_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c8_0, fixed_tlTTwoP5c8_1, fixed_tlTTwoP5c8_2, fixed_tlTTwoP5c8_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c9_0, fixed_tlTTwoP5c9_1, fixed_tlTTwoP5c9_2, fixed_tlTTwoP5c9_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c10_0, fixed_tlTTwoP5c10_1, fixed_tlTTwoP5c10_2, fixed_tlTTwoP5c10_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c11_0, fixed_tlTTwoP5c11_1, fixed_tlTTwoP5c11_2, fixed_tlTTwoP5c11_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c12_0, fixed_tlTTwoP5c12_1, fixed_tlTTwoP5c12_2, fixed_tlTTwoP5c12_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoP5c13_0, fixed_tlTTwoP5c13_1, fixed_tlTTwoP5c13_2, fixed_tlTTwoP5c13_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c0_0, fixed_tlTTwoQ5c0_1, fixed_tlTTwoQ5c0_2, fixed_tlTTwoQ5c0_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c1_0, fixed_tlTTwoQ5c1_1, fixed_tlTTwoQ5c1_2, fixed_tlTTwoQ5c1_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c2_0, fixed_tlTTwoQ5c2_1, fixed_tlTTwoQ5c2_2, fixed_tlTTwoQ5c2_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c3_0, fixed_tlTTwoQ5c3_1, fixed_tlTTwoQ5c3_2, fixed_tlTTwoQ5c3_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c4_0, fixed_tlTTwoQ5c4_1, fixed_tlTTwoQ5c4_2, fixed_tlTTwoQ5c4_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c5_0, fixed_tlTTwoQ5c5_1, fixed_tlTTwoQ5c5_2, fixed_tlTTwoQ5c5_3, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlTTwoQ5c6_0, fixed_tlTTwoQ5c6_1, fixed_tlTTwoQ5c6_2, fixed_tlTTwoQ5c6_3, add_zero, zero_add, mul_zero, zero_mul]
 try ring

theorem solution :
∀ (f : ℚ),
((leftSide f).coeff 0 = (rightSide f).coeff 0) ∧
((leftSide f).coeff 1 = (rightSide f).coeff 1) ∧
((leftSide f).coeff 2 = (rightSide f).coeff 2) ∧
((leftSide f).coeff 3 = (rightSide f).coeff 3) := by
 intro f
 exact ⟨coefficient_0 f, coefficient_1 f, coefficient_2 f, coefficient_3 f⟩
#print axioms solution
