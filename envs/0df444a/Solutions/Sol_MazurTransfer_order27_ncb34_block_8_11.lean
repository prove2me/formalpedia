-- Prove2me | solution 1 for MazurTransfer.order27_ncb34_block_8_11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:09:32.460286+00:00
-- url     : https://prove2.me/submissions/2ccda8db-0444-4595-826d-4618d71a8e76

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Theorems.Thm_MazurTransfer_order27_ncb34_coefficients
namespace MazurTransfer.Order27NCb34Polynomial
open Polynomial

lemma bridge_coeff_table_p_tlNSqP3c5 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c5 f).coeff n = c_tlNSqP3c5 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).1

lemma bridge_coeff_table_p_tlN0 (f : ℚ) (n : ℕ) :
 (p_tlN0 f).coeff n = c_tlN0 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.1

lemma bridge_coeff_table_p_tlN1 (f : ℚ) (n : ℕ) :
 (p_tlN1 f).coeff n = c_tlN1 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.1

lemma bridge_coeff_table_p_tlN2 (f : ℚ) (n : ℕ) :
 (p_tlN2 f).coeff n = c_tlN2 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.1

lemma bridge_coeff_table_p_tlN3 (f : ℚ) (n : ℕ) :
 (p_tlN3 f).coeff n = c_tlN3 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.1

lemma bridge_coeff_table_p_tlT0 (f : ℚ) (n : ℕ) :
 (p_tlT0 f).coeff n = c_tlT0 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.1

lemma bridge_coeff_table_p_tlT1 (f : ℚ) (n : ℕ) :
 (p_tlT1 f).coeff n = c_tlT1 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlT2 (f : ℚ) (n : ℕ) :
 (p_tlT2 f).coeff n = c_tlT2 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlT3 (f : ℚ) (n : ℕ) :
 (p_tlT3 f).coeff n = c_tlT3 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c0 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c0 f).coeff n = c_tlNCbP34c0 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c1 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c1 f).coeff n = c_tlNCbP34c1 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c2 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c2 f).coeff n = c_tlNCbP34c2 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c3 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c3 f).coeff n = c_tlNCbP34c3 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c4 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c4 f).coeff n = c_tlNCbP34c4 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c5 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c5 f).coeff n = c_tlNCbP34c5 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c6 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c6 f).coeff n = c_tlNCbP34c6 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c7 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c7 f).coeff n = c_tlNCbP34c7 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c8 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c8 f).coeff n = c_tlNCbP34c8 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c9 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c9 f).coeff n = c_tlNCbP34c9 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c10 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c10 f).coeff n = c_tlNCbP34c10 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c11 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c11 f).coeff n = c_tlNCbP34c11 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c12 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c12 f).coeff n = c_tlNCbP34c12 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c13 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c13 f).coeff n = c_tlNCbP34c13 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c14 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c14 f).coeff n = c_tlNCbP34c14 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c15 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c15 f).coeff n = c_tlNCbP34c15 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c16 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c16 f).coeff n = c_tlNCbP34c16 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbP34c17 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c17 f).coeff n = c_tlNCbP34c17 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbQ34c0 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c0 f).coeff n = c_tlNCbQ34c0 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbQ34c1 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c1 f).coeff n = c_tlNCbQ34c1 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbQ34c2 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c2 f).coeff n = c_tlNCbQ34c2 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbQ34c3 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c3 f).coeff n = c_tlNCbQ34c3 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbQ34c4 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c4 f).coeff n = c_tlNCbQ34c4 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bridge_coeff_table_p_tlNCbQ34c5 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c5 f).coeff n = c_tlNCbQ34c5 f n := by
 exact (MazurTransfer.order27_ncb34_coefficients f n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

lemma fixed_tlNSqP3c5_0 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 0 = ((((-1948700897672900) * f ^ 43) + (1405031546216604 * f ^ 42)) + (((-946884404864984) * f ^ 41) + ((595539480061183 * f ^ 40) + ((-348964710627945) * f ^ 39)))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 0
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_1 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 1 = ((((-9629643521433701) * f ^ 43) + (8036065420867471 * f ^ 42)) + (((-6292505098060497) * f ^ 41) + ((4617947989220961 * f ^ 40) + ((-3171942832370025) * f ^ 39)))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 1
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_2 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 2 = ((((-14605063189358122) * f ^ 43) + (13850979547288302 * f ^ 42)) + (((-12365345234032767) * f ^ 41) + ((10385978262739928 * f ^ 40) + ((-8201088710751259) * f ^ 39)))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 2
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_3 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 3 = ((((-11121091865785260) * f ^ 43) + (12026695750415646 * f ^ 42)) + (((-12223807073484630) * f ^ 41) + ((11676341345831270 * f ^ 40) + ((-10479819765004701) * f ^ 39)))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 3
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_4 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 4 = (((2692939289213860 * f ^ 42) + ((-3391555698017833) * f ^ 41)) + ((3988370487944563 * f ^ 40) + ((-4380911646405201) * f ^ 39))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 4
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_5 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 5 = (((134119586348307 * f ^ 42) + ((-220103890520055) * f ^ 41)) + ((334402650466520 * f ^ 40) + ((-471020779625307) * f ^ 39))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 5
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_6 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 6 = (((2547170427118 * f ^ 42) + ((-5329916057032) * f ^ 41)) + ((10267834290671 * f ^ 40) + ((-18253431165584) * f ^ 39))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 6
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_7 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 7 = (((14008643803 * f ^ 42) + ((-41277978641) * f ^ 41)) + ((109355609702 * f ^ 40) + ((-261757036778) * f ^ 39))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 7
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_8 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 8 = (((8954549 * f ^ 42) + ((-45162866) * f ^ 41)) + ((192970533 * f ^ 40) + ((-708349671) * f ^ 39))) := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 8
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_9 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 9
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_10 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 10
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_11 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 11
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_12 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 12
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_13 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 13
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_14 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 14
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_15 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 15
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_16 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 16
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNSqP3c5_17 (f : ℚ) :
 (p_tlNSqP3c5 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNSqP3c5 f 17
 unfold c_tlNSqP3c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_0 (f : ℚ) :
 (p_tlN0 f).coeff 0 = ((((1 * f ^ 34) + (((-14) * f ^ 33) + (97 * f ^ 32))) + (((-442) * f ^ 31) + ((1484 * f ^ 30) + ((-3898) * f ^ 29)))) + (((8303 * f ^ 28) + (((-14674) * f ^ 27) + (21839 * f ^ 26))) + ((((-27628) * f ^ 25) + (29864 * f ^ 24)) + (((-27628) * f ^ 23) + (21839 * f ^ 22))))) := by
 have h := bridge_coeff_table_p_tlN0 f 0
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_1 (f : ℚ) :
 (p_tlN0 f).coeff 1 = ((((1 * f ^ 32) + ((-15) * f ^ 31)) + ((107 * f ^ 30) + (((-493) * f ^ 29) + (1665 * f ^ 28)))) + ((((-4412) * f ^ 27) + ((9560 * f ^ 26) + ((-17394) * f ^ 25))) + ((27031 * f ^ 24) + (((-36250) * f ^ 23) + (42162 * f ^ 22))))) := by
 have h := bridge_coeff_table_p_tlN0 f 1
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_2 (f : ℚ) :
 (p_tlN0 f).coeff 2 = (((((-3) * f ^ 29) + (35 * f ^ 28)) + (((-201) * f ^ 27) + (764 * f ^ 26))) + ((((-2164) * f ^ 25) + (4861 * f ^ 24)) + (((-8996) * f ^ 23) + (14076 * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlN0 f 2
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_3 (f : ℚ) :
 (p_tlN0 f).coeff 3 = (((1 * f ^ 27) + (((-8) * f ^ 26) + (32 * f ^ 25))) + (((-80) * f ^ 24) + ((115 * f ^ 23) + ((-3) * f ^ 22)))) := by
 have h := bridge_coeff_table_p_tlN0 f 3
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_4 (f : ℚ) :
 (p_tlN0 f).coeff 4 = (((-6) * f ^ 23) + (55 * f ^ 22)) := by
 have h := bridge_coeff_table_p_tlN0 f 4
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_5 (f : ℚ) :
 (p_tlN0 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 5
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_6 (f : ℚ) :
 (p_tlN0 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 6
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_7 (f : ℚ) :
 (p_tlN0 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 7
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_8 (f : ℚ) :
 (p_tlN0 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 8
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_9 (f : ℚ) :
 (p_tlN0 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 9
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_10 (f : ℚ) :
 (p_tlN0 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 10
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_11 (f : ℚ) :
 (p_tlN0 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 11
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_12 (f : ℚ) :
 (p_tlN0 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 12
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_13 (f : ℚ) :
 (p_tlN0 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 13
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_14 (f : ℚ) :
 (p_tlN0 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 14
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_15 (f : ℚ) :
 (p_tlN0 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 15
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_16 (f : ℚ) :
 (p_tlN0 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 16
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN0_17 (f : ℚ) :
 (p_tlN0 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlN0 f 17
 unfold c_tlN0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_0 (f : ℚ) :
 (p_tlN1 f).coeff 0 = ((((-14674) * f ^ 21) + ((8303 * f ^ 20) + ((-3898) * f ^ 19))) + ((1484 * f ^ 18) + (((-442) * f ^ 17) + (97 * f ^ 16)))) := by
 have h := bridge_coeff_table_p_tlN1 f 0
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_1 (f : ℚ) :
 (p_tlN1 f).coeff 1 = ((((-42560) * f ^ 21) + ((37169 * f ^ 20) + ((-27891) * f ^ 19))) + ((17785 * f ^ 18) + (((-9481) * f ^ 17) + (4125 * f ^ 16)))) := by
 have h := bridge_coeff_table_p_tlN1 f 1
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_2 (f : ℚ) :
 (p_tlN1 f).coeff 2 = ((((-18978) * f ^ 21) + ((22364 * f ^ 20) + ((-23260) * f ^ 19))) + (((21442 * f ^ 18) + ((-17471) * f ^ 17)) + ((12447 * f ^ 16) + ((-7605) * f ^ 15)))) := by
 have h := bridge_coeff_table_p_tlN1 f 2
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_3 (f : ℚ) :
 (p_tlN1 f).coeff 3 = ((((-472) * f ^ 21) + ((1455 * f ^ 20) + ((-2805) * f ^ 19))) + (((4058 * f ^ 18) + ((-4699) * f ^ 17)) + ((4531 * f ^ 16) + ((-3777) * f ^ 15)))) := by
 have h := bridge_coeff_table_p_tlN1 f 3
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_4 (f : ℚ) :
 (p_tlN1 f).coeff 4 = ((((-267) * f ^ 21) + ((892 * f ^ 20) + ((-2248) * f ^ 19))) + (((4470 * f ^ 18) + ((-7174) * f ^ 17)) + ((9389 * f ^ 16) + ((-10043) * f ^ 15)))) := by
 have h := bridge_coeff_table_p_tlN1 f 4
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_5 (f : ℚ) :
 (p_tlN1 f).coeff 5 = (((1 * f ^ 20) + (((-6) * f ^ 19) + (40 * f ^ 18))) + (((-212) * f ^ 17) + ((766 * f ^ 16) + ((-1969) * f ^ 15)))) := by
 have h := bridge_coeff_table_p_tlN1 f 5
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_6 (f : ℚ) :
 (p_tlN1 f).coeff 6 = ((-6) * f ^ 15) := by
 have h := bridge_coeff_table_p_tlN1 f 6
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_7 (f : ℚ) :
 (p_tlN1 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 7
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_8 (f : ℚ) :
 (p_tlN1 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 8
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_9 (f : ℚ) :
 (p_tlN1 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 9
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_10 (f : ℚ) :
 (p_tlN1 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 10
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_11 (f : ℚ) :
 (p_tlN1 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 11
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_12 (f : ℚ) :
 (p_tlN1 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 12
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_13 (f : ℚ) :
 (p_tlN1 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 13
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_14 (f : ℚ) :
 (p_tlN1 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 14
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_15 (f : ℚ) :
 (p_tlN1 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 15
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_16 (f : ℚ) :
 (p_tlN1 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 16
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN1_17 (f : ℚ) :
 (p_tlN1 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlN1 f 17
 unfold c_tlN1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_0 (f : ℚ) :
 (p_tlN2 f).coeff 0 = (((-14) * f ^ 15) + (1 * f ^ 14)) := by
 have h := bridge_coeff_table_p_tlN2 f 0
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_1 (f : ℚ) :
 (p_tlN2 f).coeff 1 = ((((-1412) * f ^ 15) + (358 * f ^ 14)) + (((-60) * f ^ 13) + (5 * f ^ 12))) := by
 have h := bridge_coeff_table_p_tlN2 f 1
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_2 (f : ℚ) :
 (p_tlN2 f).coeff 2 = (((3872 * f ^ 14) + ((-1576) * f ^ 13)) + ((481 * f ^ 12) + (((-98) * f ^ 11) + (10 * f ^ 10)))) := by
 have h := bridge_coeff_table_p_tlN2 f 2
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_3 (f : ℚ) :
 (p_tlN2 f).coeff 3 = (((2827 * f ^ 14) + (((-1943) * f ^ 13) + (1206 * f ^ 12))) + (((-636) * f ^ 11) + ((260 * f ^ 10) + ((-72) * f ^ 9)))) := by
 have h := bridge_coeff_table_p_tlN2 f 3
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_4 (f : ℚ) :
 (p_tlN2 f).coeff 4 = (((8732 * f ^ 14) + (((-6085) * f ^ 13) + (3313 * f ^ 12))) + (((-1352) * f ^ 11) + ((396 * f ^ 10) + ((-94) * f ^ 9)))) := by
 have h := bridge_coeff_table_p_tlN2 f 4
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_5 (f : ℚ) :
 (p_tlN2 f).coeff 5 = (((3773 * f ^ 14) + (((-5565) * f ^ 13) + (6421 * f ^ 12))) + ((((-5813) * f ^ 11) + (4093 * f ^ 10)) + (((-2183) * f ^ 9) + (834 * f ^ 8)))) := by
 have h := bridge_coeff_table_p_tlN2 f 5
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_6 (f : ℚ) :
 (p_tlN2 f).coeff 6 = (((34 * f ^ 14) + (((-117) * f ^ 13) + (310 * f ^ 12))) + ((((-654) * f ^ 11) + (1081 * f ^ 10)) + (((-1370) * f ^ 9) + (1318 * f ^ 8)))) := by
 have h := bridge_coeff_table_p_tlN2 f 6
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_7 (f : ℚ) :
 (p_tlN2 f).coeff 7 = ((1 * f ^ 11) + (((-8) * f ^ 9) + (30 * f ^ 8))) := by
 have h := bridge_coeff_table_p_tlN2 f 7
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_8 (f : ℚ) :
 (p_tlN2 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 8
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_9 (f : ℚ) :
 (p_tlN2 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 9
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_10 (f : ℚ) :
 (p_tlN2 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 10
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_11 (f : ℚ) :
 (p_tlN2 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 11
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_12 (f : ℚ) :
 (p_tlN2 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 12
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_13 (f : ℚ) :
 (p_tlN2 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 13
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_14 (f : ℚ) :
 (p_tlN2 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 14
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_15 (f : ℚ) :
 (p_tlN2 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 15
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_16 (f : ℚ) :
 (p_tlN2 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 16
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN2_17 (f : ℚ) :
 (p_tlN2 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlN2 f 17
 unfold c_tlN2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_0 (f : ℚ) :
 (p_tlN3 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 0
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_1 (f : ℚ) :
 (p_tlN3 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 1
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_2 (f : ℚ) :
 (p_tlN3 f).coeff 2 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 2
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_3 (f : ℚ) :
 (p_tlN3 f).coeff 3 = (10 * f ^ 8) := by
 have h := bridge_coeff_table_p_tlN3 f 3
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_4 (f : ℚ) :
 (p_tlN3 f).coeff 4 = ((36 * f ^ 8) + (((-19) * f ^ 7) + (5 * f ^ 6))) := by
 have h := bridge_coeff_table_p_tlN3 f 4
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_5 (f : ℚ) :
 (p_tlN3 f).coeff 5 = ((((-201) * f ^ 7) + (19 * f ^ 6)) + ((1 * f ^ 5) + (1 * f ^ 4))) := by
 have h := bridge_coeff_table_p_tlN3 f 5
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_6 (f : ℚ) :
 (p_tlN3 f).coeff 6 = ((((-946) * f ^ 7) + (489 * f ^ 6)) + (((-172) * f ^ 5) + ((34 * f ^ 4) + ((-1) * f ^ 3)))) := by
 have h := bridge_coeff_table_p_tlN3 f 6
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_7 (f : ℚ) :
 (p_tlN3 f).coeff 7 = ((((-62) * f ^ 7) + ((89 * f ^ 6) + ((-94) * f ^ 5))) + (((67 * f ^ 4) + ((-33) * f ^ 3)) + ((11 * f ^ 2) + ((-1) * f)))) := by
 have h := bridge_coeff_table_p_tlN3 f 7
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_8 (f : ℚ) :
 (p_tlN3 f).coeff 8 = ((((-2) * f ^ 5) + (2 * f ^ 4)) + (((-2) * f ^ 3) + (2 * f))) := by
 have h := bridge_coeff_table_p_tlN3 f 8
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_9 (f : ℚ) :
 (p_tlN3 f).coeff 9 = 1 := by
 have h := bridge_coeff_table_p_tlN3 f 9
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_10 (f : ℚ) :
 (p_tlN3 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 10
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_11 (f : ℚ) :
 (p_tlN3 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 11
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_12 (f : ℚ) :
 (p_tlN3 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 12
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_13 (f : ℚ) :
 (p_tlN3 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 13
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_14 (f : ℚ) :
 (p_tlN3 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 14
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_15 (f : ℚ) :
 (p_tlN3 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 15
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_16 (f : ℚ) :
 (p_tlN3 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 16
 unfold c_tlN3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlN3_17 (f : ℚ) :
 (p_tlN3 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlN3 f 17
 unfold c_tlN3 at h
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

lemma fixed_tlT0_17 (f : ℚ) :
 (p_tlT0 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlT0 f 17
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

lemma fixed_tlT1_17 (f : ℚ) :
 (p_tlT1 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlT1 f 17
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

lemma fixed_tlT2_17 (f : ℚ) :
 (p_tlT2 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlT2 f 17
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

lemma fixed_tlT3_17 (f : ℚ) :
 (p_tlT3 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlT3 f 17
 unfold c_tlT3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_0 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 0 = (((-8954549) * f ^ 114) + ((331708434 * f ^ 113) + ((-5273729139) * f ^ 112))) := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 0
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_1 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 1 = (((-26863647) * f ^ 112) + (995125302 * f ^ 111)) := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 1
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_2 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 2 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 2
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_3 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 3 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 3
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_4 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 4 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 4
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_5 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 5
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_6 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 6
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_7 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 7
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_8 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 8
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_9 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 9
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_10 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 10
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_11 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 11
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_12 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 12
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_13 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 13
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_14 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 14
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_15 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 15
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_16 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 16
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c0_17 (f : ℚ) :
 (p_tlNCbP34c0 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c0 f 17
 unfold c_tlNCbP34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_0 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 0 = (((43719628557 * f ^ 111) + (((-107156127060) * f ^ 110) + ((-2248805694527) * f ^ 109))) + (((38869315561762 * f ^ 108) + ((-377117789368418) * f ^ 107)) + ((2761393205608606 * f ^ 106) + ((-16734607696272464) * f ^ 105)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 0
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_1 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 1 = ((((-15794323770) * f ^ 110) + ((130235396761 * f ^ 109) + ((-308318770333) * f ^ 108))) + (((-6836433038131) * f ^ 107) + ((116621694568179 * f ^ 106) + ((-1124425628374402) * f ^ 105)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 1
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_2 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 2 = ((((-26863647) * f ^ 110) + ((1048852596 * f ^ 109) + ((-17623392492) * f ^ 108))) + ((156130883508 * f ^ 107) + (((-484091673513) * f ^ 106) + ((-6848978551170) * f ^ 105)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 2
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_3 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 3 = ((((-8954549) * f ^ 108) + (376481179 * f ^ 107)) + (((-6887498564) * f ^ 106) + ((68304368396 * f ^ 105) + ((-295717751915) * f ^ 104)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 3
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_4 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 4 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 4
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_5 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 5
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_6 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 6
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_7 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 7
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_8 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 8
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_9 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 9
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_10 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 10
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_11 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 11
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_12 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 12
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_13 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 13
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_14 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 14
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_15 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 15
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_16 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 16
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c1_17 (f : ℚ) :
 (p_tlNCbP34c1 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c1 f 17
 unfold c_tlNCbP34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_0 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 0 = (((88124419905897137 * f ^ 104) + ((-416226942965180066) * f ^ 103)) + ((1801432249941491714 * f ^ 102) + (((-7239882725140319593) * f ^ 101) + (27202311915802228624 * f ^ 100)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 0
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_1 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 1 = (((8192336980782549 * f ^ 104) + ((-49431471214769370) * f ^ 103)) + ((259351397525617779 * f ^ 102) + (((-1221372773563762033) * f ^ 101) + (5274060159176871632 * f ^ 100)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 1
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_2 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 2 = (((131012622792432 * f ^ 104) + (((-1315722017177431) * f ^ 103) + (9825608227530725 * f ^ 102))) + (((-60293681388097754) * f ^ 101) + ((320122724139253495 * f ^ 100) + ((-1520620696406525868) * f ^ 99)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 2
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_3 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 3 = ((((-1975540511305) * f ^ 103) + (50895813172321 * f ^ 102)) + (((-560186694310292) * f ^ 101) + ((4439475348285853 * f ^ 100) + ((-28528860282188004) * f ^ 99)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 3
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_4 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 4 = ((((-8954549) * f ^ 103) + (143662905 * f ^ 102)) + ((465374762 * f ^ 101) + (((-21880128021) * f ^ 100) + (9381477819 * f ^ 99)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 4
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_5 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 5
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_6 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 6
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_7 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 7
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_8 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 8
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_9 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 9
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_10 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 10
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_11 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 11
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_12 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 12
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_13 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 13
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_14 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 14
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_15 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 15
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_16 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 16
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c2_17 (f : ℚ) :
 (p_tlNCbP34c2 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c2 f 17
 unfold c_tlNCbP34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_0 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 0 = ((((-95774243196387400118) * f ^ 99) + (316020962353458946692 * f ^ 98)) + (((-976940775592649507017) * f ^ 97) + ((2830027673703662413624 * f ^ 96) + ((-7689938974049074770897) * f ^ 95)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 0
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_1 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 1 = ((((-21156620286086623627) * f ^ 99) + (79352398753755556102 * f ^ 98)) + (((-278870533667289137273) * f ^ 97) + ((918334619268659966232 * f ^ 96) + ((-2832975951190118984007) * f ^ 95)))) := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 1
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_2 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 2 = (((6610104964542640232 * f ^ 98) + ((-26665515278611685312) * f ^ 97)) + ((100523599873214436906 * f ^ 96) + ((-354916280797603145526) * f ^ 95))) := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 2
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_3 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 3 = (((157311447282958167 * f ^ 98) + ((-771284737235621590) * f ^ 97)) + ((3444711522340565710 * f ^ 96) + ((-14234236735197177136) * f ^ 95))) := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 3
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_4 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 4 = (((4709779156860 * f ^ 98) + ((-85058593593982) * f ^ 97)) + ((924845614117820 * f ^ 96) + ((-7496377683966240) * f ^ 95))) := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 4
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_5 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 5 = (((53727294 * f ^ 98) + ((-2142477937) * f ^ 97)) + ((39555873658 * f ^ 96) + ((-478204034653) * f ^ 95))) := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 5
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_6 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 6 = ((8954549 * f ^ 95) + ((-304844787) * f ^ 94)) := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 6
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_7 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 7
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_8 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 8
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_9 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 9
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_10 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 10
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_11 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 11
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_12 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 12
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_13 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 13
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_14 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 14
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_15 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 15
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_16 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 16
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c3_17 (f : ℚ) :
 (p_tlNCbP34c3 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c3 f 17
 unfold c_tlNCbP34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_0 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 0 = (((19634348794244487953502 * f ^ 94) + ((-47208060707375887586814) * f ^ 93)) + ((107133528713324826498580 * f ^ 92) + ((-229980590338392876671148) * f ^ 91))) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 0
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_1 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 1 = (((8189750686061571063054 * f ^ 94) + ((-22211948797241297469589) * f ^ 93)) + ((56623095874898350712870 * f ^ 92) + ((-135977868468228977594285) * f ^ 91))) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 1
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_2 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 2 = (((1173562970509233063112 * f ^ 94) + ((-3632755931555939360825) * f ^ 93)) + ((10529855926919401440422 * f ^ 92) + ((-28613339638455162076015) * f ^ 91))) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 2
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_3 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 3 = (((54882816180969241408 * f ^ 94) + ((-198115262637546389936) * f ^ 93)) + ((669934758072905942653 * f ^ 92) + ((-2121667186230334681727) * f ^ 91))) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 3
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_4 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 4 = (((49109152656363536 * f ^ 94) + ((-272539755853219394) * f ^ 93)) + ((1324627592910604941 * f ^ 92) + ((-5781096644013674881) * f ^ 91))) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 4
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_5 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 5 = (((4499672827061 * f ^ 94) + ((-36224596566841) * f ^ 93)) + ((261911771832738 * f ^ 92) + ((-1741233379058370) * f ^ 91))) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 5
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_6 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 6 = (((4224876543 * f ^ 93) + ((-26078326967) * f ^ 92)) + (((-48930763945) * f ^ 91) + (2752323783014 * f ^ 90))) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 6
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_7 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 7 = (8954549 * f ^ 90) := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 7
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_8 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 8
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_9 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 9
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_10 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 10
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_11 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 11
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_12 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 12
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_13 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 13
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_14 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 14
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_15 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 15
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_16 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 16
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c4_17 (f : ℚ) :
 (p_tlNCbP34c4 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c4 f 17
 unfold c_tlNCbP34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_0 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 0 = (((467869386754729380357666 * f ^ 90) + ((-903367965998123739410786) * f ^ 89)) + ((1657222252848954744661769 * f ^ 88) + ((-2890694699050699468708818) * f ^ 87))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 0
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_1 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 1 = (((308338013699133815774448 * f ^ 90) + ((-661632075710191327328241) * f ^ 89)) + ((1345991022458718225222393 * f ^ 88) + ((-2599802166455718208536568) * f ^ 87))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 1
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_2 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 2 = (((73030978609141577655464 * f ^ 90) + ((-175492804184497492764213) * f ^ 89)) + ((398004250829747312344473 * f ^ 88) + ((-853841586911481555512494) * f ^ 87))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 2
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_3 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 3 = (((6293587764053668027313 * f ^ 90) + ((-17501575391817295123283) * f ^ 89)) + ((45699785597864419621221 * f ^ 88) + ((-112284594781921923346986) * f ^ 87))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 3
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_4 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 4 = (((23078394110793683181 * f ^ 90) + ((-85324222818389439186) * f ^ 89)) + ((294211453162075328512 * f ^ 88) + ((-949062839397679485613) * f ^ 87))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 4
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_5 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 5 = (((10657181570022044 * f ^ 90) + ((-59368618925148010) * f ^ 89)) + ((298622777844282667 * f ^ 88) + ((-1356597297603352606) * f ^ 87))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 5
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_6 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 6 = ((((-32924799238556) * f ^ 89) + (263627511215546 * f ^ 88)) + (((-1661413862692620) * f ^ 87) + (8884024692983327 * f ^ 86))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 6
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_7 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 7 = ((((-125753807) * f ^ 89) + (250208916 * f ^ 88)) + (((-2223915122) * f ^ 87) + (188582699433 * f ^ 86))) := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 7
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_8 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 8
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_9 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 9
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_10 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 10
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_11 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 11
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_12 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 12
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_13 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 13
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_14 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 14
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_15 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 15
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_16 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 16
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c5_17 (f : ℚ) :
 (p_tlNCbP34c5 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c5 f 17
 unfold c_tlNCbP34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_0 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 0 = (((4796870933777729852025100 * f ^ 86) + ((-7575481020951752463149277) * f ^ 85)) + ((11388604994803536270700493 * f ^ 84) + ((-16300335916931112746219718) * f ^ 83))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 0
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_1 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 1 = (((4772943931545036346592723 * f ^ 86) + ((-8335377275921718419237999) * f ^ 85)) + ((13855066208699486096572321 * f ^ 84) + ((-21929225419397961427586576) * f ^ 83))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 1
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_2 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 2 = (((1736046473009345605725779 * f ^ 86) + ((-3350389054480713666231804) * f ^ 85)) + ((6144267989402604496766809 * f ^ 84) + ((-10716420505804834099712700) * f ^ 83))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 2
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_3 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 3 = (((260187493054661959789896 * f ^ 86) + ((-569862332355118546136983) * f ^ 85)) + ((1181986934285728473774028 * f ^ 84) + ((-2325411753014869586338235) * f ^ 83))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 3
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_4 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 4 = (((2866527317591032229875 * f ^ 86) + ((-8108494241661253882748) * f ^ 85)) + ((21492259943475112795576 * f ^ 84) + ((-53445384428249882978964) * f ^ 83))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 4
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_5 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 5 = (((5598844781019883384 * f ^ 86) + ((-21170921843916661532) * f ^ 85)) + ((73963639276363877912 * f ^ 84) + ((-240317367856339347467) * f ^ 83))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 5
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_6 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 6 = ((((-42310348317485884) * f ^ 85) + (184941363151348359 * f ^ 84)) + (((-752625935405348600) * f ^ 83) + (2859637868153158037 * f ^ 82))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 6
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_7 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 7 = ((((-3515594659505) * f ^ 85) + (39073857937140 * f ^ 84)) + (((-316612302135771) * f ^ 83) + (2022331048982441 * f ^ 82))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 7
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_8 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 8 = ((((-53727294) * f ^ 85) + (1712659585 * f ^ 84)) + (((-25451642273) * f ^ 83) + (250879604370 * f ^ 82))) := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 8
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_9 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 9
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_10 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 10
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_11 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 11
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_12 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 12
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_13 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 13
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_14 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 14
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_15 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 15
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_16 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 16
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c6_17 (f : ℚ) :
 (p_tlNCbP34c6 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c6 f 17
 unfold c_tlNCbP34c6 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_0 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 0 = (((22211127312009127140421447 * f ^ 82) + ((-28805129810817923807298185) * f ^ 81)) + ((35533496877286963309821793 * f ^ 80) + ((-41655042662080136725701977) * f ^ 79))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 0
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_1 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 1 = (((33060094032523873644139069 * f ^ 82) + ((-47481873760854303966426757) * f ^ 81)) + ((64967152152242817561582265 * f ^ 80) + ((-84663801262017962504353362) * f ^ 79))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 1
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_2 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 2 = (((17787338583805210021662573 * f ^ 82) + ((-28110801010314350396598754) * f ^ 81)) + ((42316315582837998973831646 * f ^ 80) + ((-60691527217037567867426049) * f ^ 79))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 2
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_3 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 3 = (((4344655926073082117439957 * f ^ 82) + ((-7715489658438019442219814) * f ^ 81)) + ((13031745883013624534208802 * f ^ 80) + ((-20944819016488855513866914) * f ^ 79))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 3
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_4 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 4 = (((124916973313616913574639 * f ^ 82) + ((-275017178244538444456596) * f ^ 81)) + ((571569625111810121804753 * f ^ 80) + ((-1123493318844768952683327) * f ^ 79))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 4
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_5 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 5 = (((729246706959481844769 * f ^ 82) + ((-2071316614787002364805) * f ^ 81)) + ((5512515998694703174037 * f ^ 80) + ((-13756415273365306272705) * f ^ 79))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 5
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_6 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 6 = ((((-10118140820089336640) * f ^ 81) + (33253309213122328683 * f ^ 80)) + (((-101487401835119265775) * f ^ 79) + (288201680642075046414 * f ^ 78))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 6
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_7 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 7 = ((((-10728709334163933) * f ^ 81) + (49267476141995938 * f ^ 80)) + (((-201931191516292193) * f ^ 79) + (755216178720307093 * f ^ 78))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 7
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_8 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 8 = ((((-1918110111510) * f ^ 81) + (12212112411495 * f ^ 80)) + (((-68643280650134) * f ^ 79) + (359815042042615 * f ^ 78))) := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 8
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_9 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 9
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_10 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 10
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_11 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 11
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_12 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 12
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_13 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 13
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_14 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 14
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_15 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 15
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_16 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 16
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c7_17 (f : ℚ) :
 (p_tlNCbP34c7 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c7 f 17
 unfold c_tlNCbP34c7 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_0 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 0 = (((46344581427697077806404059 * f ^ 78) + ((-48857933551102130797211209) * f ^ 77)) + ((48715752192386957097862350 * f ^ 76) + ((-45847857988565328421141530) * f ^ 75))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 0
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_1 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 1 = (((105028850791367499748470857 * f ^ 78) + ((-123923903012190546413800475) * f ^ 77)) + ((138907474544804843310471094 * f ^ 76) + ((-147700342819287618172410493) * f ^ 75))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 1
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_2 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 2 = (((82940335315814339904443885 * f ^ 78) + ((-107980470833558909708501498) * f ^ 77)) + ((133863721337225926391584579 * f ^ 76) + ((-157899475288614731330595694) * f ^ 75))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 2
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_3 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 3 = (((32042971202439946022607839 * f ^ 78) + ((-46672532262226402141609092) * f ^ 77)) + ((64725977675672846460254696 * f ^ 76) + ((-85447620015924790604776731) * f ^ 75))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 3
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_4 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 4 = (((2091667480849758590235973 * f ^ 78) + ((-3691998946444075658485267) * f ^ 77)) + ((6182074637149754387613423 * f ^ 76) + ((-9823114345424360395621658) * f ^ 75))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 4
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_5 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 5 = (((32221784154830498274462 * f ^ 78) + ((-70943705359892490062711) * f ^ 77)) + ((147083997104058286046382 * f ^ 76) + ((-287661994440831280774917) * f ^ 75))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 5
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_6 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 6 = ((((-764029344395754615140) * f ^ 77) + (1897415662269781958380 * f ^ 76)) + (((-4427398811596967025895) * f ^ 75) + (9728461180647730580962 * f ^ 74))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 6
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_7 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 7 = ((((-2612523671932132823) * f ^ 77) + (8406613231978251143 * f ^ 76)) + (((-25191177227730029333) * f ^ 75) + (70271970194380912598 * f ^ 74))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 7
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_8 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 8 = ((((-1778558115986836) * f ^ 77) + (8133733906678310 * f ^ 76)) + (((-33842684996506094) * f ^ 75) + (127170844600294001 * f ^ 74))) := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 8
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_9 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 9
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_10 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 10
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_11 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 11
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_12 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 12
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_13 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 13
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_14 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 14
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_15 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 15
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_16 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 16
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c8_17 (f : ℚ) :
 (p_tlNCbP34c8 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c8 f 17
 unfold c_tlNCbP34c8 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_0 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 0 = (((40640249280633262802172971 * f ^ 74) + ((-33855756138059568768074297) * f ^ 73)) + ((26447745803041981286448031 * f ^ 72) + ((-19330884842052679566786609) * f ^ 71))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 0
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_1 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 1 = (((148723422810006741384429760 * f ^ 74) + ((-141545969026019223437929867) * f ^ 73)) + ((127075079624212264100446924 * f ^ 72) + ((-107388280880285754912513273) * f ^ 71))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 1
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_2 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 2 = (((177024562195708568899990268 * f ^ 74) + ((-188386157134324100689483057) * f ^ 73)) + ((190008353588790785882377940 * f ^ 72) + ((-181339702680190850605442888) * f ^ 71))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 2
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_3 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 3 = (((107328020709517990098427712 * f ^ 74) + ((-128162403268704971725618720) * f ^ 73)) + ((145324444091248060807780995 * f ^ 72) + ((-156247618041646599428216120) * f ^ 71))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 3
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_4 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 4 = (((14813796772032724499312392 * f ^ 74) + ((-21202100902412656086197270) * f ^ 73)) + ((28793445134535590922221093 * f ^ 72) + ((-37084365775707887772913239) * f ^ 71))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 4
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_5 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 5 = (((531537830719850661393570 * f ^ 74) + ((-928984444798350848244873) * f ^ 73)) + ((1536739575649120818881271 * f ^ 72) + ((-2406810713922848497640793) * f ^ 71))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 5
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_6 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 6 = ((((-20161721033113500353545) * f ^ 73) + (39452979515502484473880 * f ^ 72)) + (((-72957712064091185067339) * f ^ 71) + (127586883030982533828878 * f ^ 70))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 6
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_7 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 7 = ((((-182494611883095560407) * f ^ 73) + (441836662604880364802 * f ^ 72)) + (((-999703189924067624745) * f ^ 71) + (2119939536719531762052 * f ^ 70))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 7
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_8 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 8 = ((((-432953441023250844) * f ^ 73) + (1348443934097750629 * f ^ 72)) + (((-3879529752685087343) * f ^ 71) + (10386596890568074620 * f ^ 70))) := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 8
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_9 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 9
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_10 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 10
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_11 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 11
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_12 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 12
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_13 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 13
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_14 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 14
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_15 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 15
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_16 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 16
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c9_17 (f : ℚ) :
 (p_tlNCbP34c9 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c9 f 17
 unfold c_tlNCbP34c9 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_0 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 0 = (((13189034286654198024613256 * f ^ 70) + ((-8378924866460904964907894) * f ^ 69)) + ((4942657392196730102107871 * f ^ 68) + ((-2698408301410838891786492) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 0
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_1 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 1 = (((85241066030905608955378618 * f ^ 70) + ((-63411520526537056242104183) * f ^ 69)) + ((44106261408416793009375827 * f ^ 68) + ((-28612321460644148941693495) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 1
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_2 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 2 = (((163477707552839839415620406 * f ^ 70) + ((-138959257669344346209835866) * f ^ 69)) + ((111163918232882764033308356 * f ^ 68) + ((-83526608560990875473245074) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 2
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_3 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 3 = (((159020157735041835866389102 * f ^ 70) + ((-152919261769562098825777081) * f ^ 69)) + ((138684723781416698326280010 * f ^ 68) + ((-118398005583394385819642443) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 3
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_4 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 4 = (((45256454042504854521410323 * f ^ 70) + ((-52260512001935017417186543) * f ^ 69)) + ((57000845276406320347013964 * f ^ 68) + ((-58592702224215527104567017) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 4
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_5 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 5 = (((3568956305327804367589105 * f ^ 70) + ((-5009549785265236571591857) * f ^ 69)) + ((6652581004573616231832321 * f ^ 68) + ((-8350667695901234956769836) * f ^ 67))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 5
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_6 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 6 = ((((-211119843682190143254702) * f ^ 69) + (330675979659148337037788 * f ^ 68)) + (((-490315499450558649036982) * f ^ 67) + (688100151793063811904824 * f ^ 66))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 6
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_7 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 7 = ((((-4224516786710288907864) * f ^ 69) + (7926455323636107536186 * f ^ 68)) + (((-14019618020506922955007) * f ^ 67) + (23387054483752132631531 * f ^ 66))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 7
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_8 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 8 = ((((-25974688586697498847) * f ^ 69) + (60722278796976761335 * f ^ 68)) + (((-132690829396711607337) * f ^ 67) + (271054520829379411799 * f ^ 66))) := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 8
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_9 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 9
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_10 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 10
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_11 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 11
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_12 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 12
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_13 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 13
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_14 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 14
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_15 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 15
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_16 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 16
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c10_17 (f : ℚ) :
 (p_tlNCbP34c10 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c10 f 17
 unfold c_tlNCbP34c10 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_0 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 0 = (((1358079178246554906634156 * f ^ 66) + ((-627128099820633528777888) * f ^ 65)) + ((264212201805620020642740 * f ^ 64) + ((-100898630597208142530927) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 0
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_1 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 1 = (((17262746395014414902617219 * f ^ 66) + ((-9655287004124454668056058) * f ^ 65)) + ((4987089542176441786401744 * f ^ 64) + ((-2367739607919285621433409) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 1
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_2 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 2 = (((58821825020961567934158714 * f ^ 66) + ((-38732260462607714509510771) * f ^ 65)) + ((23782445012936760592088034 * f ^ 64) + ((-13574634673258990323654544) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 2
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_3 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 3 = (((94978522759707174418545631 * f ^ 66) + ((-71467324340938122208271354) * f ^ 65)) + ((50352738585362492030291435 * f ^ 64) + ((-33155714460260583660025128) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 3
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_4 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 4 = (((56621563410494485640072918 * f ^ 66) + ((-51305273834472562892048230) * f ^ 65)) + ((43476369861370176091007756 * f ^ 64) + ((-34369426659679695136906728) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 4
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_5 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 5 = (((9894055154938889010243392 * f ^ 66) + ((-11042673155023288522119855) * f ^ 65)) + ((11579486278832056187295406 * f ^ 64) + ((-11372979206655399094875920) * f ^ 63))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 5
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_6 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 6 = ((((-913391325393709193224824) * f ^ 65) + (1145532301706271853118092 * f ^ 64)) + (((-1355112571564538432976593) * f ^ 63) + (1508557982833442294348710 * f ^ 62))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 6
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_7 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 7 = ((((-36800458172378929721806) * f ^ 65) + (54618755009605407316221 * f ^ 64)) + (((-76441056640943431063452) * f ^ 63) + (100819728130558905069905 * f ^ 62))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 7
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_8 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 8 = ((((-518030513292251607197) * f ^ 65) + (927680310198084042719 * f ^ 64)) + (((-1559096198585403080028) * f ^ 63) + (2462475117517602177361 * f ^ 62))) := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 8
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_9 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 9
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_10 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 10
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_11 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 11
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_12 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 12
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_13 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 13
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_14 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 14
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_15 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 15
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_16 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 16
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c11_17 (f : ℚ) :
 (p_tlNCbP34c11 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c11 f 17
 unfold c_tlNCbP34c11 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_0 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 0 = (((34674417719046421474345 * f ^ 62) + ((-10639902070948892373754) * f ^ 61)) + ((2890120534606106764938 * f ^ 60) + ((-687054537875423623362) * f ^ 59))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 0
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_1 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 1 = (((1027495735438722988099151 * f ^ 62) + ((-404834852845377021530458) * f ^ 61)) + ((143708383320431047868742 * f ^ 60) + ((-45572077024023255918879) * f ^ 59))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 1
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_2 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 2 = (((7175818100250159030600019 * f ^ 62) + ((-3497292523501205968889912) * f ^ 61)) + ((1562855453281675088000113 * f ^ 60) + ((-636070611361014317796910) * f ^ 59))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 2
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_3 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 3 = (((20360842988452502250167322 * f ^ 62) + ((-11631829747646390312003647) * f ^ 61)) + ((6163014445208582353289856 * f ^ 60) + ((-3017250596723837693746009) * f ^ 59))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 3
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_4 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 4 = (((25287261497298464547991161 * f ^ 62) + ((-17277347236334736150086329) * f ^ 61)) + ((10937924801052850251768045 * f ^ 60) + ((-6400698456882356501137006) * f ^ 59))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 4
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_5 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 5 = (((10426621485789539661324820 * f ^ 62) + ((-8891153471752493046429541) * f ^ 61)) + ((7027544185445587788161556 * f ^ 60) + ((-5131501029584755552404118) * f ^ 59))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 5
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_6 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 6 = ((((-1575745544212891031289554) * f ^ 61) + (1538859477234066979659176 * f ^ 60)) + (((-1399363149242576848629059) * f ^ 59) + (1179669262112654565235226 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 6
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_7 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 7 = ((((-125168851703687311340635) * f ^ 61) + (146001258925093572879531 * f ^ 60)) + (((-159572921323741904426798) * f ^ 59) + (162861739562574980578235 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 7
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_8 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 8 = ((((-3657762640673295556707) * f ^ 61) + (5109326062034226016023 * f ^ 60)) + (((-6705006503860955014574) * f ^ 59) + (8250242877181234032229 * f ^ 58))) := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 8
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_9 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 9
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_10 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 10
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_11 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 11
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_12 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 12
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_13 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 13
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_14 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 14
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_15 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 15
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_16 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 16
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c12_17 (f : ℚ) :
 (p_tlNCbP34c12 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c12 f 17
 unfold c_tlNCbP34c12 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_0 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 0 = (((140144033492983387085 * f ^ 58) + ((-23571979479479920399) * f ^ 57)) + ((3022062217978195211 * f ^ 56) + ((-256327997125259781) * f ^ 55))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 0
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_1 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 1 = (((12791838969609804892772 * f ^ 58) + ((-3143894237561961069551) * f ^ 57)) + ((665136654750769581307 * f ^ 56) + ((-116923728325491356956) * f ^ 55))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 1
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_2 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 2 = (((233865682735992462790052 * f ^ 58) + ((-76950158638165199094347) * f ^ 57)) + ((22424686941563208365866 * f ^ 56) + ((-5723593463654162555717) * f ^ 55))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 2
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_3 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 3 = (((1358667302080840136024827 * f ^ 58) + ((-559537354696737797938392) * f ^ 57)) + ((209233624632756526850957 * f ^ 56) + ((-70389155158128492144249) * f ^ 55))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 3
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_4 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 4 = (((3452352514279845843276278 * f ^ 58) + ((-1710322933230402632662040) * f ^ 57)) + ((774984858611103079295793 * f ^ 56) + ((-319673386342823138200756) * f ^ 55))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 4
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_5 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 5 = (((3450906672363543672065287 * f ^ 58) + ((-2130859405736817076582080) * f ^ 57)) + ((1204159404730419795953880 * f ^ 56) + ((-620235551039855756460278) * f ^ 55))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 5
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_6 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 6 = ((((-917706223845413281324751) * f ^ 57) + (655840213839421013411415 * f ^ 56)) + (((-428712511553265233490501) * f ^ 55) + (255281399338048291774581 * f ^ 54))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 6
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_7 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 7 = ((((-154596995239303933315168) * f ^ 57) + (135891732853251570999030 * f ^ 56)) + (((-110088965895772603691843) * f ^ 55) + (81785170745777803688055 * f ^ 54))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 7
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_8 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 8 = ((((-9490012856701426489890) * f ^ 57) + (10164307094670664381843 * f ^ 56)) + (((-10088479296026211987416) * f ^ 55) + (9231130784248724751935 * f ^ 54))) := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 8
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_9 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 9
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_10 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 10
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_11 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 11
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_12 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 12
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_13 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 13
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_14 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 14
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_15 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 15
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_16 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 16
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c13_17 (f : ℚ) :
 (p_tlNCbP34c13 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c13 f 17
 unfold c_tlNCbP34c13 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_0 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 0 = ((12470329193088090 * f ^ 54) + ((-697929421255890) * f ^ 53)) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 0
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_1 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 1 = (((15793066835847301523 * f ^ 54) + ((-1392187963958719927) * f ^ 53)) + ((62710600227745172 * f ^ 52) + ((-3838611816907395) * f ^ 51))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 1
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_2 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 2 = (((1261417860238027142120 * f ^ 54) + ((-233390062292280294424) * f ^ 53)) + ((33727922703149409173 * f ^ 52) + ((-3168593635892909038) * f ^ 51))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 2
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_3 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 3 = (((21057980516381721531247 * f ^ 54) + ((-5527659826763885592496) * f ^ 53)) + ((1255322011857538243401 * f ^ 52) + ((-242072222243160265976) * f ^ 51))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 3
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_4 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 4 = (((119432700558896529865974 * f ^ 54) + ((-40183821378858607525656) * f ^ 53)) + ((12075374626421457058822 * f ^ 52) + ((-3196365753235756584811) * f ^ 51))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 4
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_5 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 5 = (((289616565666459555979655 * f ^ 54) + ((-121750687325362283584378) * f ^ 53)) + ((45729115573106178537631 * f ^ 52) + ((-15253735869665900811900) * f ^ 51))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 5
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_6 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 6 = ((((-137883863279251194182228) * f ^ 53) + (67195401636704833287716 * f ^ 52)) + (((-29310666568079193401802) * f ^ 51) + (11303349498367594999292 * f ^ 50))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 6
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_7 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 7 = ((((-55419242897567816737689) * f ^ 53) + (34058837670975575209264 * f ^ 52)) + (((-18873946628589927575329) * f ^ 51) + (9377902580729687811600 * f ^ 50))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 7
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_8 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 8 = ((((-7745602288019931836505) * f ^ 53) + (5928128096825368966187 * f ^ 52)) + (((-4115746446213680658885) * f ^ 51) + (2574966117195746694287 * f ^ 50))) := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 8
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_9 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 9
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_10 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 10
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_11 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 11
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_12 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 12
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_13 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 13
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_14 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 14
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_15 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 15
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_16 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 16
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c14_17 (f : ℚ) :
 (p_tlNCbP34c14 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c14 f 17
 unfold c_tlNCbP34c14 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_0 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 0
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_1 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 1
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_2 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 2 = ((128242886795544235 * f ^ 50) + ((-8724117765698625) * f ^ 49)) := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 2
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_3 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 3 = (((37604039530786400216 * f ^ 50) + ((-3889914002507494094) * f ^ 49)) + ((135621093477114965 * f ^ 48) + ((-10468941318838350) * f ^ 47))) := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 3
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_4 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 4 = (((730584488102535868961 * f ^ 50) + ((-141676584536925650681) * f ^ 49)) + ((23068391661297206659 * f ^ 48) + ((-2744839757266436882) * f ^ 47))) := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 4
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_5 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 5 = (((4507710605300180572846 * f ^ 50) + ((-1175990451306658304009) * f ^ 49)) + ((264981025253747583006 * f ^ 48) + ((-48860617596093935695) * f ^ 47))) := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 5
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_6 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 6 = ((((-3793102506779600545999) * f ^ 49) + (1094626835514715702925 * f ^ 48)) + (((-273308834917328011818) * f ^ 47) + (60218537144095806638 * f ^ 46))) := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 6
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_7 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 7 = ((((-4155286550838814781251) * f ^ 49) + (1629227215544749200665 * f ^ 48)) + (((-555283903446810128749) * f ^ 47) + (158950715052109276592 * f ^ 46))) := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 7
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_8 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 8 = ((((-1439251794360868729665) * f ^ 49) + (710188694713815987756 * f ^ 48)) + (((-305023090863354742030) * f ^ 47) + (113117296664475959407 * f ^ 46))) := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 8
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_9 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 9
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_10 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 10
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_11 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 11
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_12 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 12
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_13 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 13
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_14 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 14
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_15 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 15
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_16 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 16
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c15_17 (f : ℚ) :
 (p_tlNCbP34c15 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c15 f 17
 unfold c_tlNCbP34c15 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_0 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 0
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_1 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 1
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_2 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 2 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 2
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_3 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 3 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 3
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_4 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 4 = ((77805988749837800 * f ^ 46) + ((-6979294212558900) * f ^ 45)) := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 4
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_5 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 5 = (((7444575749293347836 * f ^ 46) + ((-1081040095933092958) * f ^ 45)) + ((23338182980938270 * f ^ 44) + ((-2442752974395615) * f ^ 43))) := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 5
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_6 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 6 = ((((-10606602767917796670) * f ^ 45) + (1066960624741187490 * f ^ 44)) + (((-203080554507807551) * f ^ 43) + (3499636657956227 * f ^ 42))) := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 6
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_7 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 7 = ((((-36450258722361051544) * f ^ 45) + (7151394107774050915 * f ^ 44)) + (((-1454211897748243826) * f ^ 43) + (46129104650063093 * f ^ 42))) := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 7
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_8 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 8 = ((((-36350440181639560945) * f ^ 45) + (10269529833241752391 * f ^ 44)) + (((-2249875213391488882) * f ^ 43) + (209215579555396483 * f ^ 42))) := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 8
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_9 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 9
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_10 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 10
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_11 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 11
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_12 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 12
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_13 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 13
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_14 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 14
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_15 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 15
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_16 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 16
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c16_17 (f : ℚ) :
 (p_tlNCbP34c16 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c16 f 17
 unfold c_tlNCbP34c16 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_0 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 0 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 0
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_1 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 1 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 1
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_2 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 2 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 2
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_3 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 3 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 3
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_4 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 4 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 4
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_5 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 5
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_6 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 6 = ((-348964710627945) * f ^ 41) := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 6
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_7 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 7 = (((-9699882393106273) * f ^ 41) + (348964710627945 * f ^ 40)) := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 7
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_8 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 8 = (((-65550985890140279) * f ^ 41) + (2474013411114135 * f ^ 40)) := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 8
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_9 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 9
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_10 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 10
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_11 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 11
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_12 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 12
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_13 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 13
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_14 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 14
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_15 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 15
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_16 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 16
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbP34c17_17 (f : ℚ) :
 (p_tlNCbP34c17 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbP34c17 f 17
 unfold c_tlNCbP34c17 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_0 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 0 = (((((8954549 * f ^ 81) + ((-215299297) * f ^ 80)) + ((1722656162 * f ^ 79) + ((-34228961) * f ^ 78))) + ((((-125151937541) * f ^ 77) + (1508665663464 * f ^ 76)) + (((-11342201251539) * f ^ 75) + (64223300272121 * f ^ 74)))) + (((((-304427070088968) * f ^ 73) + (1294918521155475 * f ^ 72)) + (((-5106640907540586) * f ^ 71) + (18867338181767651 * f ^ 70))) + ((((-64718992334584355) * f ^ 69) + (203632671630964270 * f ^ 68)) + (((-585233846788881142) * f ^ 67) + ((1537010438472903790 * f ^ 66) + ((-3707926148153467605) * f ^ 65)))))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 0
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_1 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 1 = ((((8954549 * f ^ 76) + (((-89935611) * f ^ 75) + (499375804 * f ^ 74))) + (((-8177715999) * f ^ 73) + ((114377744099 * f ^ 72) + ((-1139109609654) * f ^ 71)))) + (((8790750022231 * f ^ 70) + (((-52031571142655) * f ^ 69) + (247686709376671 * f ^ 68))) + (((-996045290386307) * f ^ 67) + ((3481719878356598 * f ^ 66) + ((-10962057689572575) * f ^ 65))))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 1
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_2 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 2 = ((((-53727294) * f ^ 71) + ((1121659351 * f ^ 70) + ((-11385161455) * f ^ 69))) + (((82630472557 * f ^ 68) + ((-461908599374) * f ^ 67)) + ((2068224427586 * f ^ 66) + ((-8729770287628) * f ^ 65)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 2
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_3 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 3 = (((8954549 * f ^ 67) + ((-125753807) * f ^ 66)) + ((429299896 * f ^ 65) + (2138102370 * f ^ 64))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 3
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_4 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 4 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 4
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_5 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 5 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 5
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_6 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 6
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_7 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 7
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_8 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 8
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_9 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 9
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_10 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 10
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_11 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 11
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_12 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 12
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_13 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 13
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_14 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 14
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_15 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 15
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_16 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 16
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c0_17 (f : ℚ) :
 (p_tlNCbQ34c0 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c0 f 17
 unfold c_tlNCbQ34c0 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_0 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 0 = ((((8274984080561032828 * f ^ 64) + ((-17186337619981139396) * f ^ 63)) + ((33373263299108125802 * f ^ 62) + ((-60676160977948193904) * f ^ 61))) + (((103226501464245697214 * f ^ 60) + ((-164192136236359052406) * f ^ 59)) + ((244055860806141002317 * f ^ 58) + ((-339265991846129581610) * f ^ 57)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 0
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_1 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 1 = ((((31877080048346386 * f ^ 64) + ((-86312227959142324) * f ^ 63)) + ((217745912234489651 * f ^ 62) + ((-507434892581428750) * f ^ 61))) + (((1087839769368228824 * f ^ 60) + ((-2150656072760385621) * f ^ 59)) + ((3937662353815269160 * f ^ 58) + ((-6731679908693711066) * f ^ 57)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 1
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_2 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 2 = ((((36527214022007 * f ^ 64) + ((-145270407355472) * f ^ 63)) + ((531478197566178 * f ^ 62) + ((-1709738473469742) * f ^ 61))) + (((4873741439946534 * f ^ 60) + ((-12577278140041546) * f ^ 59)) + ((29718645783970333 * f ^ 58) + ((-65763158352634563) * f ^ 57)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 2
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_3 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 3 = ((((-37766963022) * f ^ 63) + ((300306296393 * f ^ 62) + ((-1491219226841) * f ^ 61))) + (((6055754932591 * f ^ 60) + ((-22284365028896) * f ^ 59)) + ((74692333072941 * f ^ 58) + ((-246079415551446) * f ^ 57)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 3
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_4 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 4 = (((8954549 * f ^ 62) + (((-63071964) * f ^ 61) + (659387323 * f ^ 60))) + ((((-5838677691) * f ^ 59) + (35685348698 * f ^ 58)) + (((-268692258435) * f ^ 57) + (1461925239336 * f ^ 56)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 4
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_5 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 5 = (((-53727294) * f ^ 57) + (584386411 * f ^ 56)) := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 5
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_6 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 6 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 6
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_7 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 7
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_8 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 8
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_9 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 9
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_10 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 10
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_11 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 11
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_12 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 12
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_13 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 13
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_14 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 14
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_15 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 15
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_16 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 16
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c1_17 (f : ℚ) :
 (p_tlNCbQ34c1 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c1 f 17
 unfold c_tlNCbQ34c1 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_0 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 0 = (((441433458808725648281 * f ^ 56) + (((-537361731762444533149) * f ^ 55) + (610344927036102301610 * f ^ 54))) + (((-643071977522854574760) * f ^ 53) + ((623258844950971117592 * f ^ 52) + ((-550291784130336033208) * f ^ 51)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 0
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_1 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 1 = (((10791901823213549604 * f ^ 56) + (((-16259053414037074430) * f ^ 55) + (22999076106417594167 * f ^ 54))) + (((-30382190524815564555) * f ^ 53) + ((37282387332571290346 * f ^ 52) + ((-42216774792282774456) * f ^ 51)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 1
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_2 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 2 = (((136657917731088096 * f ^ 56) + (((-266612475375272007) * f ^ 55) + (485855719228846288 * f ^ 54))) + (((-812117285626507972) * f ^ 53) + ((1243287247288919493 * f ^ 52) + ((-1735025782392328388) * f ^ 51)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 2
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_3 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 3 = (((753137991743376 * f ^ 56) + (((-2084048443190245) * f ^ 55) + (5145115874841716 * f ^ 54))) + (((-10982822691991763) * f ^ 53) + ((20878871059480831 * f ^ 52) + ((-35607831265060025) * f ^ 51)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 3
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_4 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 4 = ((((-6189651577473) * f ^ 55) + ((21579994724270 * f ^ 54) + ((-58560321611053) * f ^ 53))) + ((139844473470202 * f ^ 52) + (((-297486957235768) * f ^ 51) + (586983257889069 * f ^ 50)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 4
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_5 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 5 = ((((-3974251270) * f ^ 55) + ((20719861750 * f ^ 54) + ((-62279840545) * f ^ 53))) + ((180310826548 * f ^ 52) + (((-511092869412) * f ^ 51) + (1499774779574 * f ^ 50)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 5
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_6 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 6 = (((8954549 * f ^ 53) + ((-45162866) * f ^ 52)) + ((121334141 * f ^ 51) + ((-24682979) * f ^ 50))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 6
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_7 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 7 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 7
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_8 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 8
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_9 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 9
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_10 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 10
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_11 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 11
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_12 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 12
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_13 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 13
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_14 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 14
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_15 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 15
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_16 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 16
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c2_17 (f : ℚ) :
 (p_tlNCbQ34c2 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c2 f 17
 unfold c_tlNCbQ34c2 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_0 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 0 = (((438351925932180372200 * f ^ 50) + ((-312559807811031513877) * f ^ 49)) + ((198240525769635459553 * f ^ 48) + (((-111300483681516212959) * f ^ 47) + (55049035279590611626 * f ^ 46)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 0
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_1 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 1 = (((43754752742342169124 * f ^ 50) + ((-41139991406266681568) * f ^ 49)) + ((34681332565344610523 * f ^ 48) + (((-25892403677214984301) * f ^ 47) + (16933781880540295783 * f ^ 46)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 1
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_2 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 2 = (((2220900118317141763 * f ^ 50) + (((-2622500598586875155) * f ^ 49) + (2846612384531230462 * f ^ 48))) + (((-2816302334254183067) * f ^ 47) + ((2490962120276247331 * f ^ 46) + ((-1913476987328106050) * f ^ 45)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 2
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_3 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 3 = (((55754292816414735 * f ^ 50) + (((-81605622008329787) * f ^ 49) + (109699934908595908 * f ^ 48))) + (((-140573717588869524) * f ^ 47) + ((158519201880066677 * f ^ 46) + ((-154084515860482549) * f ^ 45)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 3
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_4 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 4 = ((((-1115777091018577) * f ^ 49) + (1932668157621679 * f ^ 48)) + (((-3271401102066664) * f ^ 47) + ((4605372983107755 * f ^ 46) + ((-5439795408549426) * f ^ 45)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 4
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_5 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 5 = ((((-4843698757189) * f ^ 49) + (12510561549672 * f ^ 48)) + (((-31062520354421) * f ^ 47) + ((56179453238207 * f ^ 46) + ((-83475341025339) * f ^ 45)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 5
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_6 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 6 = ((((-3885991360) * f ^ 49) + (17238629873 * f ^ 48)) + (((-75115559042) * f ^ 47) + ((195137243650 * f ^ 46) + ((-436340298324) * f ^ 45)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 6
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_7 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 7 = (((-17909098) * f ^ 47) + ((108234830 * f ^ 46) + ((-494175896) * f ^ 45))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 7
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_8 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 8 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 8
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_9 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 9
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_10 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 10
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_11 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 11
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_12 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 12
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_13 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 13
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_14 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 14
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_15 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 15
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_16 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 16
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c3_17 (f : ℚ) :
 (p_tlNCbQ34c3 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c3 f 17
 unfold c_tlNCbQ34c3 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_0 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 0 = ((((-23543862951970875532) * f ^ 45) + (8391929635344377902 * f ^ 44)) + (((-2288397067471775937) * f ^ 43) + ((488492505525288930 * f ^ 42) + ((-151995294536939094) * f ^ 41)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 0
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_1 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 1 = ((((-9554084072331991564) * f ^ 45) + (4607726455059834268 * f ^ 44)) + (((-1867942604251735019) * f ^ 43) + ((648483553972096786 * f ^ 42) + ((-179734737569897029) * f ^ 41)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 1
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_2 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 2 = (((1250057829049453722 * f ^ 44) + ((-666715292301287624) * f ^ 43)) + ((274866374127175764 * f ^ 42) + ((-67947551798828514) * f ^ 41))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 2
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_3 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 3 = (((125166640302163362 * f ^ 44) + ((-82163446665406052) * f ^ 43)) + ((40953326369077290 * f ^ 42) + ((-12607075432857827) * f ^ 41))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 3
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_4 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 4 = (((5436234975185883 * f ^ 44) + ((-3459753901904953) * f ^ 43)) + ((4193816944551467 * f ^ 42) + ((-3043588318227170) * f ^ 41))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 4
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_5 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 5 = (((110179730807388 * f ^ 44) + ((-79863042365616) * f ^ 43)) + ((173639824387490 * f ^ 42) + (((-204128155523312) * f ^ 41) + (298157545172130 * f ^ 40)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 5
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_6 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 6 = (((926953563028 * f ^ 44) + ((-783878124645) * f ^ 43)) + ((3023329940514 * f ^ 42) + (((-5123439752568) * f ^ 41) + (9745028566786 * f ^ 40)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 6
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_7 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 7 = (((1892966140 * f ^ 44) + ((-1784731310) * f ^ 43)) + ((15335017413 * f ^ 42) + (((-40892037575) * f ^ 41) + (107938910360 * f ^ 40)))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 7
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_8 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 8 = ((8954549 * f ^ 42) + (((-45162866) * f ^ 41) + (192970533 * f ^ 40))) := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 8
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_9 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 9
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_10 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 10
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_11 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 11
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_12 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 12
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_13 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 13
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_14 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 14
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_15 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 15
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_16 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 16
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c4_17 (f : ℚ) :
 (p_tlNCbQ34c4 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c4 f 17
 unfold c_tlNCbQ34c4 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_0 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 0 = ((2452742526072392 * f ^ 40) + ((-348964710627945) * f ^ 39)) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 0
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_1 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 1 = (((-1304409667276856) * f ^ 40) + ((-3171942832370025) * f ^ 39)) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 1
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_2 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 2 = (((-6192749620864273) * f ^ 40) + ((-8201088710751259) * f ^ 39)) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 2
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_3 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 3 = ((3385538832646175 * f ^ 40) + ((-10479819765004701) * f ^ 39)) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 3
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_4 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 4 = ((3064582359859533 * f ^ 40) + ((-4380911646405201) * f ^ 39)) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 4
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_5 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 5 = ((-471020779625307) * f ^ 39) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 5
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_6 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 6 = ((-18253431165584) * f ^ 39) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 6
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_7 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 7 = ((-261757036778) * f ^ 39) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 7
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_8 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 8 = ((-708349671) * f ^ 39) := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 8
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_9 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 9 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 9
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_10 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 10 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 10
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_11 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 11 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 11
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_12 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 12 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 12
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_13 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 13 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 13
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_14 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 14 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 14
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_15 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 15 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 15
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_16 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 16 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 16
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

lemma fixed_tlNCbQ34c5_17 (f : ℚ) :
 (p_tlNCbQ34c5 f).coeff 17 = 0 := by
 have h := bridge_coeff_table_p_tlNCbQ34c5 f 17
 unfold c_tlNCbQ34c5 at h
 norm_num only [ite_true, ite_false, add_zero, zero_add] at h
 exact h

end MazurTransfer.Order27NCb34Polynomial
open Polynomial MazurTransfer.Order27NCb34Polynomial

lemma coefficient_8 (f : ℚ) : (leftSide f).coeff 8 = (rightSide f).coeff 8 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP3c5_0, fixed_tlNSqP3c5_1, fixed_tlNSqP3c5_2, fixed_tlNSqP3c5_3, fixed_tlNSqP3c5_4, fixed_tlNSqP3c5_5, fixed_tlNSqP3c5_6, fixed_tlNSqP3c5_7, fixed_tlNSqP3c5_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN0_0, fixed_tlN0_1, fixed_tlN0_2, fixed_tlN0_3, fixed_tlN0_4, fixed_tlN0_5, fixed_tlN0_6, fixed_tlN0_7, fixed_tlN0_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN1_0, fixed_tlN1_1, fixed_tlN1_2, fixed_tlN1_3, fixed_tlN1_4, fixed_tlN1_5, fixed_tlN1_6, fixed_tlN1_7, fixed_tlN1_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN2_0, fixed_tlN2_1, fixed_tlN2_2, fixed_tlN2_3, fixed_tlN2_4, fixed_tlN2_5, fixed_tlN2_6, fixed_tlN2_7, fixed_tlN2_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN3_0, fixed_tlN3_1, fixed_tlN3_2, fixed_tlN3_3, fixed_tlN3_4, fixed_tlN3_5, fixed_tlN3_6, fixed_tlN3_7, fixed_tlN3_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, fixed_tlT0_1, fixed_tlT0_2, fixed_tlT0_3, fixed_tlT0_4, fixed_tlT0_5, fixed_tlT0_6, fixed_tlT0_7, fixed_tlT0_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, fixed_tlT1_1, fixed_tlT1_2, fixed_tlT1_3, fixed_tlT1_4, fixed_tlT1_5, fixed_tlT1_6, fixed_tlT1_7, fixed_tlT1_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, fixed_tlT2_1, fixed_tlT2_2, fixed_tlT2_3, fixed_tlT2_4, fixed_tlT2_5, fixed_tlT2_6, fixed_tlT2_7, fixed_tlT2_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, fixed_tlT3_1, fixed_tlT3_2, fixed_tlT3_3, fixed_tlT3_4, fixed_tlT3_5, fixed_tlT3_6, fixed_tlT3_7, fixed_tlT3_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c0_0, fixed_tlNCbP34c0_1, fixed_tlNCbP34c0_2, fixed_tlNCbP34c0_3, fixed_tlNCbP34c0_4, fixed_tlNCbP34c0_5, fixed_tlNCbP34c0_6, fixed_tlNCbP34c0_7, fixed_tlNCbP34c0_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c1_0, fixed_tlNCbP34c1_1, fixed_tlNCbP34c1_2, fixed_tlNCbP34c1_3, fixed_tlNCbP34c1_4, fixed_tlNCbP34c1_5, fixed_tlNCbP34c1_6, fixed_tlNCbP34c1_7, fixed_tlNCbP34c1_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c2_0, fixed_tlNCbP34c2_1, fixed_tlNCbP34c2_2, fixed_tlNCbP34c2_3, fixed_tlNCbP34c2_4, fixed_tlNCbP34c2_5, fixed_tlNCbP34c2_6, fixed_tlNCbP34c2_7, fixed_tlNCbP34c2_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c3_0, fixed_tlNCbP34c3_1, fixed_tlNCbP34c3_2, fixed_tlNCbP34c3_3, fixed_tlNCbP34c3_4, fixed_tlNCbP34c3_5, fixed_tlNCbP34c3_6, fixed_tlNCbP34c3_7, fixed_tlNCbP34c3_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c4_0, fixed_tlNCbP34c4_1, fixed_tlNCbP34c4_2, fixed_tlNCbP34c4_3, fixed_tlNCbP34c4_4, fixed_tlNCbP34c4_5, fixed_tlNCbP34c4_6, fixed_tlNCbP34c4_7, fixed_tlNCbP34c4_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c5_0, fixed_tlNCbP34c5_1, fixed_tlNCbP34c5_2, fixed_tlNCbP34c5_3, fixed_tlNCbP34c5_4, fixed_tlNCbP34c5_5, fixed_tlNCbP34c5_6, fixed_tlNCbP34c5_7, fixed_tlNCbP34c5_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c6_0, fixed_tlNCbP34c6_1, fixed_tlNCbP34c6_2, fixed_tlNCbP34c6_3, fixed_tlNCbP34c6_4, fixed_tlNCbP34c6_5, fixed_tlNCbP34c6_6, fixed_tlNCbP34c6_7, fixed_tlNCbP34c6_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c7_0, fixed_tlNCbP34c7_1, fixed_tlNCbP34c7_2, fixed_tlNCbP34c7_3, fixed_tlNCbP34c7_4, fixed_tlNCbP34c7_5, fixed_tlNCbP34c7_6, fixed_tlNCbP34c7_7, fixed_tlNCbP34c7_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c8_0, fixed_tlNCbP34c8_1, fixed_tlNCbP34c8_2, fixed_tlNCbP34c8_3, fixed_tlNCbP34c8_4, fixed_tlNCbP34c8_5, fixed_tlNCbP34c8_6, fixed_tlNCbP34c8_7, fixed_tlNCbP34c8_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c9_0, fixed_tlNCbP34c9_1, fixed_tlNCbP34c9_2, fixed_tlNCbP34c9_3, fixed_tlNCbP34c9_4, fixed_tlNCbP34c9_5, fixed_tlNCbP34c9_6, fixed_tlNCbP34c9_7, fixed_tlNCbP34c9_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c10_0, fixed_tlNCbP34c10_1, fixed_tlNCbP34c10_2, fixed_tlNCbP34c10_3, fixed_tlNCbP34c10_4, fixed_tlNCbP34c10_5, fixed_tlNCbP34c10_6, fixed_tlNCbP34c10_7, fixed_tlNCbP34c10_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c11_0, fixed_tlNCbP34c11_1, fixed_tlNCbP34c11_2, fixed_tlNCbP34c11_3, fixed_tlNCbP34c11_4, fixed_tlNCbP34c11_5, fixed_tlNCbP34c11_6, fixed_tlNCbP34c11_7, fixed_tlNCbP34c11_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c12_0, fixed_tlNCbP34c12_1, fixed_tlNCbP34c12_2, fixed_tlNCbP34c12_3, fixed_tlNCbP34c12_4, fixed_tlNCbP34c12_5, fixed_tlNCbP34c12_6, fixed_tlNCbP34c12_7, fixed_tlNCbP34c12_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c13_0, fixed_tlNCbP34c13_1, fixed_tlNCbP34c13_2, fixed_tlNCbP34c13_3, fixed_tlNCbP34c13_4, fixed_tlNCbP34c13_5, fixed_tlNCbP34c13_6, fixed_tlNCbP34c13_7, fixed_tlNCbP34c13_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c14_0, fixed_tlNCbP34c14_1, fixed_tlNCbP34c14_2, fixed_tlNCbP34c14_3, fixed_tlNCbP34c14_4, fixed_tlNCbP34c14_5, fixed_tlNCbP34c14_6, fixed_tlNCbP34c14_7, fixed_tlNCbP34c14_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c15_0, fixed_tlNCbP34c15_1, fixed_tlNCbP34c15_2, fixed_tlNCbP34c15_3, fixed_tlNCbP34c15_4, fixed_tlNCbP34c15_5, fixed_tlNCbP34c15_6, fixed_tlNCbP34c15_7, fixed_tlNCbP34c15_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c16_0, fixed_tlNCbP34c16_1, fixed_tlNCbP34c16_2, fixed_tlNCbP34c16_3, fixed_tlNCbP34c16_4, fixed_tlNCbP34c16_5, fixed_tlNCbP34c16_6, fixed_tlNCbP34c16_7, fixed_tlNCbP34c16_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c17_0, fixed_tlNCbP34c17_1, fixed_tlNCbP34c17_2, fixed_tlNCbP34c17_3, fixed_tlNCbP34c17_4, fixed_tlNCbP34c17_5, fixed_tlNCbP34c17_6, fixed_tlNCbP34c17_7, fixed_tlNCbP34c17_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c0_0, fixed_tlNCbQ34c0_1, fixed_tlNCbQ34c0_2, fixed_tlNCbQ34c0_3, fixed_tlNCbQ34c0_4, fixed_tlNCbQ34c0_5, fixed_tlNCbQ34c0_6, fixed_tlNCbQ34c0_7, fixed_tlNCbQ34c0_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c1_0, fixed_tlNCbQ34c1_1, fixed_tlNCbQ34c1_2, fixed_tlNCbQ34c1_3, fixed_tlNCbQ34c1_4, fixed_tlNCbQ34c1_5, fixed_tlNCbQ34c1_6, fixed_tlNCbQ34c1_7, fixed_tlNCbQ34c1_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c2_0, fixed_tlNCbQ34c2_1, fixed_tlNCbQ34c2_2, fixed_tlNCbQ34c2_3, fixed_tlNCbQ34c2_4, fixed_tlNCbQ34c2_5, fixed_tlNCbQ34c2_6, fixed_tlNCbQ34c2_7, fixed_tlNCbQ34c2_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c3_0, fixed_tlNCbQ34c3_1, fixed_tlNCbQ34c3_2, fixed_tlNCbQ34c3_3, fixed_tlNCbQ34c3_4, fixed_tlNCbQ34c3_5, fixed_tlNCbQ34c3_6, fixed_tlNCbQ34c3_7, fixed_tlNCbQ34c3_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c4_0, fixed_tlNCbQ34c4_1, fixed_tlNCbQ34c4_2, fixed_tlNCbQ34c4_3, fixed_tlNCbQ34c4_4, fixed_tlNCbQ34c4_5, fixed_tlNCbQ34c4_6, fixed_tlNCbQ34c4_7, fixed_tlNCbQ34c4_8, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c5_0, fixed_tlNCbQ34c5_1, fixed_tlNCbQ34c5_2, fixed_tlNCbQ34c5_3, fixed_tlNCbQ34c5_4, fixed_tlNCbQ34c5_5, fixed_tlNCbQ34c5_6, fixed_tlNCbQ34c5_7, fixed_tlNCbQ34c5_8, add_zero, zero_add, mul_zero, zero_mul]
 try ring

lemma coefficient_9 (f : ℚ) : (leftSide f).coeff 9 = (rightSide f).coeff 9 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP3c5_0, fixed_tlNSqP3c5_1, fixed_tlNSqP3c5_2, fixed_tlNSqP3c5_3, fixed_tlNSqP3c5_4, fixed_tlNSqP3c5_5, fixed_tlNSqP3c5_6, fixed_tlNSqP3c5_7, fixed_tlNSqP3c5_8, fixed_tlNSqP3c5_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN0_0, fixed_tlN0_1, fixed_tlN0_2, fixed_tlN0_3, fixed_tlN0_4, fixed_tlN0_5, fixed_tlN0_6, fixed_tlN0_7, fixed_tlN0_8, fixed_tlN0_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN1_0, fixed_tlN1_1, fixed_tlN1_2, fixed_tlN1_3, fixed_tlN1_4, fixed_tlN1_5, fixed_tlN1_6, fixed_tlN1_7, fixed_tlN1_8, fixed_tlN1_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN2_0, fixed_tlN2_1, fixed_tlN2_2, fixed_tlN2_3, fixed_tlN2_4, fixed_tlN2_5, fixed_tlN2_6, fixed_tlN2_7, fixed_tlN2_8, fixed_tlN2_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN3_0, fixed_tlN3_1, fixed_tlN3_2, fixed_tlN3_3, fixed_tlN3_4, fixed_tlN3_5, fixed_tlN3_6, fixed_tlN3_7, fixed_tlN3_8, fixed_tlN3_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, fixed_tlT0_1, fixed_tlT0_2, fixed_tlT0_3, fixed_tlT0_4, fixed_tlT0_5, fixed_tlT0_6, fixed_tlT0_7, fixed_tlT0_8, fixed_tlT0_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, fixed_tlT1_1, fixed_tlT1_2, fixed_tlT1_3, fixed_tlT1_4, fixed_tlT1_5, fixed_tlT1_6, fixed_tlT1_7, fixed_tlT1_8, fixed_tlT1_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, fixed_tlT2_1, fixed_tlT2_2, fixed_tlT2_3, fixed_tlT2_4, fixed_tlT2_5, fixed_tlT2_6, fixed_tlT2_7, fixed_tlT2_8, fixed_tlT2_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, fixed_tlT3_1, fixed_tlT3_2, fixed_tlT3_3, fixed_tlT3_4, fixed_tlT3_5, fixed_tlT3_6, fixed_tlT3_7, fixed_tlT3_8, fixed_tlT3_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c0_0, fixed_tlNCbP34c0_1, fixed_tlNCbP34c0_2, fixed_tlNCbP34c0_3, fixed_tlNCbP34c0_4, fixed_tlNCbP34c0_5, fixed_tlNCbP34c0_6, fixed_tlNCbP34c0_7, fixed_tlNCbP34c0_8, fixed_tlNCbP34c0_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c1_0, fixed_tlNCbP34c1_1, fixed_tlNCbP34c1_2, fixed_tlNCbP34c1_3, fixed_tlNCbP34c1_4, fixed_tlNCbP34c1_5, fixed_tlNCbP34c1_6, fixed_tlNCbP34c1_7, fixed_tlNCbP34c1_8, fixed_tlNCbP34c1_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c2_0, fixed_tlNCbP34c2_1, fixed_tlNCbP34c2_2, fixed_tlNCbP34c2_3, fixed_tlNCbP34c2_4, fixed_tlNCbP34c2_5, fixed_tlNCbP34c2_6, fixed_tlNCbP34c2_7, fixed_tlNCbP34c2_8, fixed_tlNCbP34c2_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c3_0, fixed_tlNCbP34c3_1, fixed_tlNCbP34c3_2, fixed_tlNCbP34c3_3, fixed_tlNCbP34c3_4, fixed_tlNCbP34c3_5, fixed_tlNCbP34c3_6, fixed_tlNCbP34c3_7, fixed_tlNCbP34c3_8, fixed_tlNCbP34c3_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c4_0, fixed_tlNCbP34c4_1, fixed_tlNCbP34c4_2, fixed_tlNCbP34c4_3, fixed_tlNCbP34c4_4, fixed_tlNCbP34c4_5, fixed_tlNCbP34c4_6, fixed_tlNCbP34c4_7, fixed_tlNCbP34c4_8, fixed_tlNCbP34c4_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c5_0, fixed_tlNCbP34c5_1, fixed_tlNCbP34c5_2, fixed_tlNCbP34c5_3, fixed_tlNCbP34c5_4, fixed_tlNCbP34c5_5, fixed_tlNCbP34c5_6, fixed_tlNCbP34c5_7, fixed_tlNCbP34c5_8, fixed_tlNCbP34c5_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c6_0, fixed_tlNCbP34c6_1, fixed_tlNCbP34c6_2, fixed_tlNCbP34c6_3, fixed_tlNCbP34c6_4, fixed_tlNCbP34c6_5, fixed_tlNCbP34c6_6, fixed_tlNCbP34c6_7, fixed_tlNCbP34c6_8, fixed_tlNCbP34c6_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c7_0, fixed_tlNCbP34c7_1, fixed_tlNCbP34c7_2, fixed_tlNCbP34c7_3, fixed_tlNCbP34c7_4, fixed_tlNCbP34c7_5, fixed_tlNCbP34c7_6, fixed_tlNCbP34c7_7, fixed_tlNCbP34c7_8, fixed_tlNCbP34c7_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c8_0, fixed_tlNCbP34c8_1, fixed_tlNCbP34c8_2, fixed_tlNCbP34c8_3, fixed_tlNCbP34c8_4, fixed_tlNCbP34c8_5, fixed_tlNCbP34c8_6, fixed_tlNCbP34c8_7, fixed_tlNCbP34c8_8, fixed_tlNCbP34c8_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c9_0, fixed_tlNCbP34c9_1, fixed_tlNCbP34c9_2, fixed_tlNCbP34c9_3, fixed_tlNCbP34c9_4, fixed_tlNCbP34c9_5, fixed_tlNCbP34c9_6, fixed_tlNCbP34c9_7, fixed_tlNCbP34c9_8, fixed_tlNCbP34c9_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c10_0, fixed_tlNCbP34c10_1, fixed_tlNCbP34c10_2, fixed_tlNCbP34c10_3, fixed_tlNCbP34c10_4, fixed_tlNCbP34c10_5, fixed_tlNCbP34c10_6, fixed_tlNCbP34c10_7, fixed_tlNCbP34c10_8, fixed_tlNCbP34c10_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c11_0, fixed_tlNCbP34c11_1, fixed_tlNCbP34c11_2, fixed_tlNCbP34c11_3, fixed_tlNCbP34c11_4, fixed_tlNCbP34c11_5, fixed_tlNCbP34c11_6, fixed_tlNCbP34c11_7, fixed_tlNCbP34c11_8, fixed_tlNCbP34c11_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c12_0, fixed_tlNCbP34c12_1, fixed_tlNCbP34c12_2, fixed_tlNCbP34c12_3, fixed_tlNCbP34c12_4, fixed_tlNCbP34c12_5, fixed_tlNCbP34c12_6, fixed_tlNCbP34c12_7, fixed_tlNCbP34c12_8, fixed_tlNCbP34c12_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c13_0, fixed_tlNCbP34c13_1, fixed_tlNCbP34c13_2, fixed_tlNCbP34c13_3, fixed_tlNCbP34c13_4, fixed_tlNCbP34c13_5, fixed_tlNCbP34c13_6, fixed_tlNCbP34c13_7, fixed_tlNCbP34c13_8, fixed_tlNCbP34c13_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c14_0, fixed_tlNCbP34c14_1, fixed_tlNCbP34c14_2, fixed_tlNCbP34c14_3, fixed_tlNCbP34c14_4, fixed_tlNCbP34c14_5, fixed_tlNCbP34c14_6, fixed_tlNCbP34c14_7, fixed_tlNCbP34c14_8, fixed_tlNCbP34c14_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c15_0, fixed_tlNCbP34c15_1, fixed_tlNCbP34c15_2, fixed_tlNCbP34c15_3, fixed_tlNCbP34c15_4, fixed_tlNCbP34c15_5, fixed_tlNCbP34c15_6, fixed_tlNCbP34c15_7, fixed_tlNCbP34c15_8, fixed_tlNCbP34c15_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c16_0, fixed_tlNCbP34c16_1, fixed_tlNCbP34c16_2, fixed_tlNCbP34c16_3, fixed_tlNCbP34c16_4, fixed_tlNCbP34c16_5, fixed_tlNCbP34c16_6, fixed_tlNCbP34c16_7, fixed_tlNCbP34c16_8, fixed_tlNCbP34c16_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c17_0, fixed_tlNCbP34c17_1, fixed_tlNCbP34c17_2, fixed_tlNCbP34c17_3, fixed_tlNCbP34c17_4, fixed_tlNCbP34c17_5, fixed_tlNCbP34c17_6, fixed_tlNCbP34c17_7, fixed_tlNCbP34c17_8, fixed_tlNCbP34c17_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c0_0, fixed_tlNCbQ34c0_1, fixed_tlNCbQ34c0_2, fixed_tlNCbQ34c0_3, fixed_tlNCbQ34c0_4, fixed_tlNCbQ34c0_5, fixed_tlNCbQ34c0_6, fixed_tlNCbQ34c0_7, fixed_tlNCbQ34c0_8, fixed_tlNCbQ34c0_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c1_0, fixed_tlNCbQ34c1_1, fixed_tlNCbQ34c1_2, fixed_tlNCbQ34c1_3, fixed_tlNCbQ34c1_4, fixed_tlNCbQ34c1_5, fixed_tlNCbQ34c1_6, fixed_tlNCbQ34c1_7, fixed_tlNCbQ34c1_8, fixed_tlNCbQ34c1_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c2_0, fixed_tlNCbQ34c2_1, fixed_tlNCbQ34c2_2, fixed_tlNCbQ34c2_3, fixed_tlNCbQ34c2_4, fixed_tlNCbQ34c2_5, fixed_tlNCbQ34c2_6, fixed_tlNCbQ34c2_7, fixed_tlNCbQ34c2_8, fixed_tlNCbQ34c2_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c3_0, fixed_tlNCbQ34c3_1, fixed_tlNCbQ34c3_2, fixed_tlNCbQ34c3_3, fixed_tlNCbQ34c3_4, fixed_tlNCbQ34c3_5, fixed_tlNCbQ34c3_6, fixed_tlNCbQ34c3_7, fixed_tlNCbQ34c3_8, fixed_tlNCbQ34c3_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c4_0, fixed_tlNCbQ34c4_1, fixed_tlNCbQ34c4_2, fixed_tlNCbQ34c4_3, fixed_tlNCbQ34c4_4, fixed_tlNCbQ34c4_5, fixed_tlNCbQ34c4_6, fixed_tlNCbQ34c4_7, fixed_tlNCbQ34c4_8, fixed_tlNCbQ34c4_9, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c5_0, fixed_tlNCbQ34c5_1, fixed_tlNCbQ34c5_2, fixed_tlNCbQ34c5_3, fixed_tlNCbQ34c5_4, fixed_tlNCbQ34c5_5, fixed_tlNCbQ34c5_6, fixed_tlNCbQ34c5_7, fixed_tlNCbQ34c5_8, fixed_tlNCbQ34c5_9, add_zero, zero_add, mul_zero, zero_mul]
 try ring

lemma coefficient_10 (f : ℚ) : (leftSide f).coeff 10 = (rightSide f).coeff 10 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP3c5_0, fixed_tlNSqP3c5_1, fixed_tlNSqP3c5_2, fixed_tlNSqP3c5_3, fixed_tlNSqP3c5_4, fixed_tlNSqP3c5_5, fixed_tlNSqP3c5_6, fixed_tlNSqP3c5_7, fixed_tlNSqP3c5_8, fixed_tlNSqP3c5_9, fixed_tlNSqP3c5_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN0_0, fixed_tlN0_1, fixed_tlN0_2, fixed_tlN0_3, fixed_tlN0_4, fixed_tlN0_5, fixed_tlN0_6, fixed_tlN0_7, fixed_tlN0_8, fixed_tlN0_9, fixed_tlN0_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN1_0, fixed_tlN1_1, fixed_tlN1_2, fixed_tlN1_3, fixed_tlN1_4, fixed_tlN1_5, fixed_tlN1_6, fixed_tlN1_7, fixed_tlN1_8, fixed_tlN1_9, fixed_tlN1_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN2_0, fixed_tlN2_1, fixed_tlN2_2, fixed_tlN2_3, fixed_tlN2_4, fixed_tlN2_5, fixed_tlN2_6, fixed_tlN2_7, fixed_tlN2_8, fixed_tlN2_9, fixed_tlN2_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN3_0, fixed_tlN3_1, fixed_tlN3_2, fixed_tlN3_3, fixed_tlN3_4, fixed_tlN3_5, fixed_tlN3_6, fixed_tlN3_7, fixed_tlN3_8, fixed_tlN3_9, fixed_tlN3_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, fixed_tlT0_1, fixed_tlT0_2, fixed_tlT0_3, fixed_tlT0_4, fixed_tlT0_5, fixed_tlT0_6, fixed_tlT0_7, fixed_tlT0_8, fixed_tlT0_9, fixed_tlT0_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, fixed_tlT1_1, fixed_tlT1_2, fixed_tlT1_3, fixed_tlT1_4, fixed_tlT1_5, fixed_tlT1_6, fixed_tlT1_7, fixed_tlT1_8, fixed_tlT1_9, fixed_tlT1_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, fixed_tlT2_1, fixed_tlT2_2, fixed_tlT2_3, fixed_tlT2_4, fixed_tlT2_5, fixed_tlT2_6, fixed_tlT2_7, fixed_tlT2_8, fixed_tlT2_9, fixed_tlT2_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, fixed_tlT3_1, fixed_tlT3_2, fixed_tlT3_3, fixed_tlT3_4, fixed_tlT3_5, fixed_tlT3_6, fixed_tlT3_7, fixed_tlT3_8, fixed_tlT3_9, fixed_tlT3_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c0_0, fixed_tlNCbP34c0_1, fixed_tlNCbP34c0_2, fixed_tlNCbP34c0_3, fixed_tlNCbP34c0_4, fixed_tlNCbP34c0_5, fixed_tlNCbP34c0_6, fixed_tlNCbP34c0_7, fixed_tlNCbP34c0_8, fixed_tlNCbP34c0_9, fixed_tlNCbP34c0_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c1_0, fixed_tlNCbP34c1_1, fixed_tlNCbP34c1_2, fixed_tlNCbP34c1_3, fixed_tlNCbP34c1_4, fixed_tlNCbP34c1_5, fixed_tlNCbP34c1_6, fixed_tlNCbP34c1_7, fixed_tlNCbP34c1_8, fixed_tlNCbP34c1_9, fixed_tlNCbP34c1_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c2_0, fixed_tlNCbP34c2_1, fixed_tlNCbP34c2_2, fixed_tlNCbP34c2_3, fixed_tlNCbP34c2_4, fixed_tlNCbP34c2_5, fixed_tlNCbP34c2_6, fixed_tlNCbP34c2_7, fixed_tlNCbP34c2_8, fixed_tlNCbP34c2_9, fixed_tlNCbP34c2_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c3_0, fixed_tlNCbP34c3_1, fixed_tlNCbP34c3_2, fixed_tlNCbP34c3_3, fixed_tlNCbP34c3_4, fixed_tlNCbP34c3_5, fixed_tlNCbP34c3_6, fixed_tlNCbP34c3_7, fixed_tlNCbP34c3_8, fixed_tlNCbP34c3_9, fixed_tlNCbP34c3_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c4_0, fixed_tlNCbP34c4_1, fixed_tlNCbP34c4_2, fixed_tlNCbP34c4_3, fixed_tlNCbP34c4_4, fixed_tlNCbP34c4_5, fixed_tlNCbP34c4_6, fixed_tlNCbP34c4_7, fixed_tlNCbP34c4_8, fixed_tlNCbP34c4_9, fixed_tlNCbP34c4_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c5_0, fixed_tlNCbP34c5_1, fixed_tlNCbP34c5_2, fixed_tlNCbP34c5_3, fixed_tlNCbP34c5_4, fixed_tlNCbP34c5_5, fixed_tlNCbP34c5_6, fixed_tlNCbP34c5_7, fixed_tlNCbP34c5_8, fixed_tlNCbP34c5_9, fixed_tlNCbP34c5_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c6_0, fixed_tlNCbP34c6_1, fixed_tlNCbP34c6_2, fixed_tlNCbP34c6_3, fixed_tlNCbP34c6_4, fixed_tlNCbP34c6_5, fixed_tlNCbP34c6_6, fixed_tlNCbP34c6_7, fixed_tlNCbP34c6_8, fixed_tlNCbP34c6_9, fixed_tlNCbP34c6_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c7_0, fixed_tlNCbP34c7_1, fixed_tlNCbP34c7_2, fixed_tlNCbP34c7_3, fixed_tlNCbP34c7_4, fixed_tlNCbP34c7_5, fixed_tlNCbP34c7_6, fixed_tlNCbP34c7_7, fixed_tlNCbP34c7_8, fixed_tlNCbP34c7_9, fixed_tlNCbP34c7_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c8_0, fixed_tlNCbP34c8_1, fixed_tlNCbP34c8_2, fixed_tlNCbP34c8_3, fixed_tlNCbP34c8_4, fixed_tlNCbP34c8_5, fixed_tlNCbP34c8_6, fixed_tlNCbP34c8_7, fixed_tlNCbP34c8_8, fixed_tlNCbP34c8_9, fixed_tlNCbP34c8_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c9_0, fixed_tlNCbP34c9_1, fixed_tlNCbP34c9_2, fixed_tlNCbP34c9_3, fixed_tlNCbP34c9_4, fixed_tlNCbP34c9_5, fixed_tlNCbP34c9_6, fixed_tlNCbP34c9_7, fixed_tlNCbP34c9_8, fixed_tlNCbP34c9_9, fixed_tlNCbP34c9_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c10_0, fixed_tlNCbP34c10_1, fixed_tlNCbP34c10_2, fixed_tlNCbP34c10_3, fixed_tlNCbP34c10_4, fixed_tlNCbP34c10_5, fixed_tlNCbP34c10_6, fixed_tlNCbP34c10_7, fixed_tlNCbP34c10_8, fixed_tlNCbP34c10_9, fixed_tlNCbP34c10_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c11_0, fixed_tlNCbP34c11_1, fixed_tlNCbP34c11_2, fixed_tlNCbP34c11_3, fixed_tlNCbP34c11_4, fixed_tlNCbP34c11_5, fixed_tlNCbP34c11_6, fixed_tlNCbP34c11_7, fixed_tlNCbP34c11_8, fixed_tlNCbP34c11_9, fixed_tlNCbP34c11_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c12_0, fixed_tlNCbP34c12_1, fixed_tlNCbP34c12_2, fixed_tlNCbP34c12_3, fixed_tlNCbP34c12_4, fixed_tlNCbP34c12_5, fixed_tlNCbP34c12_6, fixed_tlNCbP34c12_7, fixed_tlNCbP34c12_8, fixed_tlNCbP34c12_9, fixed_tlNCbP34c12_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c13_0, fixed_tlNCbP34c13_1, fixed_tlNCbP34c13_2, fixed_tlNCbP34c13_3, fixed_tlNCbP34c13_4, fixed_tlNCbP34c13_5, fixed_tlNCbP34c13_6, fixed_tlNCbP34c13_7, fixed_tlNCbP34c13_8, fixed_tlNCbP34c13_9, fixed_tlNCbP34c13_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c14_0, fixed_tlNCbP34c14_1, fixed_tlNCbP34c14_2, fixed_tlNCbP34c14_3, fixed_tlNCbP34c14_4, fixed_tlNCbP34c14_5, fixed_tlNCbP34c14_6, fixed_tlNCbP34c14_7, fixed_tlNCbP34c14_8, fixed_tlNCbP34c14_9, fixed_tlNCbP34c14_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c15_0, fixed_tlNCbP34c15_1, fixed_tlNCbP34c15_2, fixed_tlNCbP34c15_3, fixed_tlNCbP34c15_4, fixed_tlNCbP34c15_5, fixed_tlNCbP34c15_6, fixed_tlNCbP34c15_7, fixed_tlNCbP34c15_8, fixed_tlNCbP34c15_9, fixed_tlNCbP34c15_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c16_0, fixed_tlNCbP34c16_1, fixed_tlNCbP34c16_2, fixed_tlNCbP34c16_3, fixed_tlNCbP34c16_4, fixed_tlNCbP34c16_5, fixed_tlNCbP34c16_6, fixed_tlNCbP34c16_7, fixed_tlNCbP34c16_8, fixed_tlNCbP34c16_9, fixed_tlNCbP34c16_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c17_0, fixed_tlNCbP34c17_1, fixed_tlNCbP34c17_2, fixed_tlNCbP34c17_3, fixed_tlNCbP34c17_4, fixed_tlNCbP34c17_5, fixed_tlNCbP34c17_6, fixed_tlNCbP34c17_7, fixed_tlNCbP34c17_8, fixed_tlNCbP34c17_9, fixed_tlNCbP34c17_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c0_0, fixed_tlNCbQ34c0_1, fixed_tlNCbQ34c0_2, fixed_tlNCbQ34c0_3, fixed_tlNCbQ34c0_4, fixed_tlNCbQ34c0_5, fixed_tlNCbQ34c0_6, fixed_tlNCbQ34c0_7, fixed_tlNCbQ34c0_8, fixed_tlNCbQ34c0_9, fixed_tlNCbQ34c0_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c1_0, fixed_tlNCbQ34c1_1, fixed_tlNCbQ34c1_2, fixed_tlNCbQ34c1_3, fixed_tlNCbQ34c1_4, fixed_tlNCbQ34c1_5, fixed_tlNCbQ34c1_6, fixed_tlNCbQ34c1_7, fixed_tlNCbQ34c1_8, fixed_tlNCbQ34c1_9, fixed_tlNCbQ34c1_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c2_0, fixed_tlNCbQ34c2_1, fixed_tlNCbQ34c2_2, fixed_tlNCbQ34c2_3, fixed_tlNCbQ34c2_4, fixed_tlNCbQ34c2_5, fixed_tlNCbQ34c2_6, fixed_tlNCbQ34c2_7, fixed_tlNCbQ34c2_8, fixed_tlNCbQ34c2_9, fixed_tlNCbQ34c2_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c3_0, fixed_tlNCbQ34c3_1, fixed_tlNCbQ34c3_2, fixed_tlNCbQ34c3_3, fixed_tlNCbQ34c3_4, fixed_tlNCbQ34c3_5, fixed_tlNCbQ34c3_6, fixed_tlNCbQ34c3_7, fixed_tlNCbQ34c3_8, fixed_tlNCbQ34c3_9, fixed_tlNCbQ34c3_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c4_0, fixed_tlNCbQ34c4_1, fixed_tlNCbQ34c4_2, fixed_tlNCbQ34c4_3, fixed_tlNCbQ34c4_4, fixed_tlNCbQ34c4_5, fixed_tlNCbQ34c4_6, fixed_tlNCbQ34c4_7, fixed_tlNCbQ34c4_8, fixed_tlNCbQ34c4_9, fixed_tlNCbQ34c4_10, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c5_0, fixed_tlNCbQ34c5_1, fixed_tlNCbQ34c5_2, fixed_tlNCbQ34c5_3, fixed_tlNCbQ34c5_4, fixed_tlNCbQ34c5_5, fixed_tlNCbQ34c5_6, fixed_tlNCbQ34c5_7, fixed_tlNCbQ34c5_8, fixed_tlNCbQ34c5_9, fixed_tlNCbQ34c5_10, add_zero, zero_add, mul_zero, zero_mul]
 try ring

lemma coefficient_11 (f : ℚ) : (leftSide f).coeff 11 = (rightSide f).coeff 11 := by
 norm_num only [leftSide, rightSide, Polynomial.coeff_mul, Polynomial.coeff_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero, ite_true, ite_false, add_zero, zero_add]
 try simp only [fixed_tlNSqP3c5_0, fixed_tlNSqP3c5_1, fixed_tlNSqP3c5_2, fixed_tlNSqP3c5_3, fixed_tlNSqP3c5_4, fixed_tlNSqP3c5_5, fixed_tlNSqP3c5_6, fixed_tlNSqP3c5_7, fixed_tlNSqP3c5_8, fixed_tlNSqP3c5_9, fixed_tlNSqP3c5_10, fixed_tlNSqP3c5_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN0_0, fixed_tlN0_1, fixed_tlN0_2, fixed_tlN0_3, fixed_tlN0_4, fixed_tlN0_5, fixed_tlN0_6, fixed_tlN0_7, fixed_tlN0_8, fixed_tlN0_9, fixed_tlN0_10, fixed_tlN0_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN1_0, fixed_tlN1_1, fixed_tlN1_2, fixed_tlN1_3, fixed_tlN1_4, fixed_tlN1_5, fixed_tlN1_6, fixed_tlN1_7, fixed_tlN1_8, fixed_tlN1_9, fixed_tlN1_10, fixed_tlN1_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN2_0, fixed_tlN2_1, fixed_tlN2_2, fixed_tlN2_3, fixed_tlN2_4, fixed_tlN2_5, fixed_tlN2_6, fixed_tlN2_7, fixed_tlN2_8, fixed_tlN2_9, fixed_tlN2_10, fixed_tlN2_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlN3_0, fixed_tlN3_1, fixed_tlN3_2, fixed_tlN3_3, fixed_tlN3_4, fixed_tlN3_5, fixed_tlN3_6, fixed_tlN3_7, fixed_tlN3_8, fixed_tlN3_9, fixed_tlN3_10, fixed_tlN3_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT0_0, fixed_tlT0_1, fixed_tlT0_2, fixed_tlT0_3, fixed_tlT0_4, fixed_tlT0_5, fixed_tlT0_6, fixed_tlT0_7, fixed_tlT0_8, fixed_tlT0_9, fixed_tlT0_10, fixed_tlT0_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT1_0, fixed_tlT1_1, fixed_tlT1_2, fixed_tlT1_3, fixed_tlT1_4, fixed_tlT1_5, fixed_tlT1_6, fixed_tlT1_7, fixed_tlT1_8, fixed_tlT1_9, fixed_tlT1_10, fixed_tlT1_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT2_0, fixed_tlT2_1, fixed_tlT2_2, fixed_tlT2_3, fixed_tlT2_4, fixed_tlT2_5, fixed_tlT2_6, fixed_tlT2_7, fixed_tlT2_8, fixed_tlT2_9, fixed_tlT2_10, fixed_tlT2_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlT3_0, fixed_tlT3_1, fixed_tlT3_2, fixed_tlT3_3, fixed_tlT3_4, fixed_tlT3_5, fixed_tlT3_6, fixed_tlT3_7, fixed_tlT3_8, fixed_tlT3_9, fixed_tlT3_10, fixed_tlT3_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c0_0, fixed_tlNCbP34c0_1, fixed_tlNCbP34c0_2, fixed_tlNCbP34c0_3, fixed_tlNCbP34c0_4, fixed_tlNCbP34c0_5, fixed_tlNCbP34c0_6, fixed_tlNCbP34c0_7, fixed_tlNCbP34c0_8, fixed_tlNCbP34c0_9, fixed_tlNCbP34c0_10, fixed_tlNCbP34c0_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c1_0, fixed_tlNCbP34c1_1, fixed_tlNCbP34c1_2, fixed_tlNCbP34c1_3, fixed_tlNCbP34c1_4, fixed_tlNCbP34c1_5, fixed_tlNCbP34c1_6, fixed_tlNCbP34c1_7, fixed_tlNCbP34c1_8, fixed_tlNCbP34c1_9, fixed_tlNCbP34c1_10, fixed_tlNCbP34c1_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c2_0, fixed_tlNCbP34c2_1, fixed_tlNCbP34c2_2, fixed_tlNCbP34c2_3, fixed_tlNCbP34c2_4, fixed_tlNCbP34c2_5, fixed_tlNCbP34c2_6, fixed_tlNCbP34c2_7, fixed_tlNCbP34c2_8, fixed_tlNCbP34c2_9, fixed_tlNCbP34c2_10, fixed_tlNCbP34c2_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c3_0, fixed_tlNCbP34c3_1, fixed_tlNCbP34c3_2, fixed_tlNCbP34c3_3, fixed_tlNCbP34c3_4, fixed_tlNCbP34c3_5, fixed_tlNCbP34c3_6, fixed_tlNCbP34c3_7, fixed_tlNCbP34c3_8, fixed_tlNCbP34c3_9, fixed_tlNCbP34c3_10, fixed_tlNCbP34c3_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c4_0, fixed_tlNCbP34c4_1, fixed_tlNCbP34c4_2, fixed_tlNCbP34c4_3, fixed_tlNCbP34c4_4, fixed_tlNCbP34c4_5, fixed_tlNCbP34c4_6, fixed_tlNCbP34c4_7, fixed_tlNCbP34c4_8, fixed_tlNCbP34c4_9, fixed_tlNCbP34c4_10, fixed_tlNCbP34c4_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c5_0, fixed_tlNCbP34c5_1, fixed_tlNCbP34c5_2, fixed_tlNCbP34c5_3, fixed_tlNCbP34c5_4, fixed_tlNCbP34c5_5, fixed_tlNCbP34c5_6, fixed_tlNCbP34c5_7, fixed_tlNCbP34c5_8, fixed_tlNCbP34c5_9, fixed_tlNCbP34c5_10, fixed_tlNCbP34c5_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c6_0, fixed_tlNCbP34c6_1, fixed_tlNCbP34c6_2, fixed_tlNCbP34c6_3, fixed_tlNCbP34c6_4, fixed_tlNCbP34c6_5, fixed_tlNCbP34c6_6, fixed_tlNCbP34c6_7, fixed_tlNCbP34c6_8, fixed_tlNCbP34c6_9, fixed_tlNCbP34c6_10, fixed_tlNCbP34c6_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c7_0, fixed_tlNCbP34c7_1, fixed_tlNCbP34c7_2, fixed_tlNCbP34c7_3, fixed_tlNCbP34c7_4, fixed_tlNCbP34c7_5, fixed_tlNCbP34c7_6, fixed_tlNCbP34c7_7, fixed_tlNCbP34c7_8, fixed_tlNCbP34c7_9, fixed_tlNCbP34c7_10, fixed_tlNCbP34c7_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c8_0, fixed_tlNCbP34c8_1, fixed_tlNCbP34c8_2, fixed_tlNCbP34c8_3, fixed_tlNCbP34c8_4, fixed_tlNCbP34c8_5, fixed_tlNCbP34c8_6, fixed_tlNCbP34c8_7, fixed_tlNCbP34c8_8, fixed_tlNCbP34c8_9, fixed_tlNCbP34c8_10, fixed_tlNCbP34c8_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c9_0, fixed_tlNCbP34c9_1, fixed_tlNCbP34c9_2, fixed_tlNCbP34c9_3, fixed_tlNCbP34c9_4, fixed_tlNCbP34c9_5, fixed_tlNCbP34c9_6, fixed_tlNCbP34c9_7, fixed_tlNCbP34c9_8, fixed_tlNCbP34c9_9, fixed_tlNCbP34c9_10, fixed_tlNCbP34c9_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c10_0, fixed_tlNCbP34c10_1, fixed_tlNCbP34c10_2, fixed_tlNCbP34c10_3, fixed_tlNCbP34c10_4, fixed_tlNCbP34c10_5, fixed_tlNCbP34c10_6, fixed_tlNCbP34c10_7, fixed_tlNCbP34c10_8, fixed_tlNCbP34c10_9, fixed_tlNCbP34c10_10, fixed_tlNCbP34c10_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c11_0, fixed_tlNCbP34c11_1, fixed_tlNCbP34c11_2, fixed_tlNCbP34c11_3, fixed_tlNCbP34c11_4, fixed_tlNCbP34c11_5, fixed_tlNCbP34c11_6, fixed_tlNCbP34c11_7, fixed_tlNCbP34c11_8, fixed_tlNCbP34c11_9, fixed_tlNCbP34c11_10, fixed_tlNCbP34c11_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c12_0, fixed_tlNCbP34c12_1, fixed_tlNCbP34c12_2, fixed_tlNCbP34c12_3, fixed_tlNCbP34c12_4, fixed_tlNCbP34c12_5, fixed_tlNCbP34c12_6, fixed_tlNCbP34c12_7, fixed_tlNCbP34c12_8, fixed_tlNCbP34c12_9, fixed_tlNCbP34c12_10, fixed_tlNCbP34c12_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c13_0, fixed_tlNCbP34c13_1, fixed_tlNCbP34c13_2, fixed_tlNCbP34c13_3, fixed_tlNCbP34c13_4, fixed_tlNCbP34c13_5, fixed_tlNCbP34c13_6, fixed_tlNCbP34c13_7, fixed_tlNCbP34c13_8, fixed_tlNCbP34c13_9, fixed_tlNCbP34c13_10, fixed_tlNCbP34c13_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c14_0, fixed_tlNCbP34c14_1, fixed_tlNCbP34c14_2, fixed_tlNCbP34c14_3, fixed_tlNCbP34c14_4, fixed_tlNCbP34c14_5, fixed_tlNCbP34c14_6, fixed_tlNCbP34c14_7, fixed_tlNCbP34c14_8, fixed_tlNCbP34c14_9, fixed_tlNCbP34c14_10, fixed_tlNCbP34c14_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c15_0, fixed_tlNCbP34c15_1, fixed_tlNCbP34c15_2, fixed_tlNCbP34c15_3, fixed_tlNCbP34c15_4, fixed_tlNCbP34c15_5, fixed_tlNCbP34c15_6, fixed_tlNCbP34c15_7, fixed_tlNCbP34c15_8, fixed_tlNCbP34c15_9, fixed_tlNCbP34c15_10, fixed_tlNCbP34c15_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c16_0, fixed_tlNCbP34c16_1, fixed_tlNCbP34c16_2, fixed_tlNCbP34c16_3, fixed_tlNCbP34c16_4, fixed_tlNCbP34c16_5, fixed_tlNCbP34c16_6, fixed_tlNCbP34c16_7, fixed_tlNCbP34c16_8, fixed_tlNCbP34c16_9, fixed_tlNCbP34c16_10, fixed_tlNCbP34c16_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbP34c17_0, fixed_tlNCbP34c17_1, fixed_tlNCbP34c17_2, fixed_tlNCbP34c17_3, fixed_tlNCbP34c17_4, fixed_tlNCbP34c17_5, fixed_tlNCbP34c17_6, fixed_tlNCbP34c17_7, fixed_tlNCbP34c17_8, fixed_tlNCbP34c17_9, fixed_tlNCbP34c17_10, fixed_tlNCbP34c17_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c0_0, fixed_tlNCbQ34c0_1, fixed_tlNCbQ34c0_2, fixed_tlNCbQ34c0_3, fixed_tlNCbQ34c0_4, fixed_tlNCbQ34c0_5, fixed_tlNCbQ34c0_6, fixed_tlNCbQ34c0_7, fixed_tlNCbQ34c0_8, fixed_tlNCbQ34c0_9, fixed_tlNCbQ34c0_10, fixed_tlNCbQ34c0_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c1_0, fixed_tlNCbQ34c1_1, fixed_tlNCbQ34c1_2, fixed_tlNCbQ34c1_3, fixed_tlNCbQ34c1_4, fixed_tlNCbQ34c1_5, fixed_tlNCbQ34c1_6, fixed_tlNCbQ34c1_7, fixed_tlNCbQ34c1_8, fixed_tlNCbQ34c1_9, fixed_tlNCbQ34c1_10, fixed_tlNCbQ34c1_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c2_0, fixed_tlNCbQ34c2_1, fixed_tlNCbQ34c2_2, fixed_tlNCbQ34c2_3, fixed_tlNCbQ34c2_4, fixed_tlNCbQ34c2_5, fixed_tlNCbQ34c2_6, fixed_tlNCbQ34c2_7, fixed_tlNCbQ34c2_8, fixed_tlNCbQ34c2_9, fixed_tlNCbQ34c2_10, fixed_tlNCbQ34c2_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c3_0, fixed_tlNCbQ34c3_1, fixed_tlNCbQ34c3_2, fixed_tlNCbQ34c3_3, fixed_tlNCbQ34c3_4, fixed_tlNCbQ34c3_5, fixed_tlNCbQ34c3_6, fixed_tlNCbQ34c3_7, fixed_tlNCbQ34c3_8, fixed_tlNCbQ34c3_9, fixed_tlNCbQ34c3_10, fixed_tlNCbQ34c3_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c4_0, fixed_tlNCbQ34c4_1, fixed_tlNCbQ34c4_2, fixed_tlNCbQ34c4_3, fixed_tlNCbQ34c4_4, fixed_tlNCbQ34c4_5, fixed_tlNCbQ34c4_6, fixed_tlNCbQ34c4_7, fixed_tlNCbQ34c4_8, fixed_tlNCbQ34c4_9, fixed_tlNCbQ34c4_10, fixed_tlNCbQ34c4_11, add_zero, zero_add, mul_zero, zero_mul]
 try simp only [fixed_tlNCbQ34c5_0, fixed_tlNCbQ34c5_1, fixed_tlNCbQ34c5_2, fixed_tlNCbQ34c5_3, fixed_tlNCbQ34c5_4, fixed_tlNCbQ34c5_5, fixed_tlNCbQ34c5_6, fixed_tlNCbQ34c5_7, fixed_tlNCbQ34c5_8, fixed_tlNCbQ34c5_9, fixed_tlNCbQ34c5_10, fixed_tlNCbQ34c5_11, add_zero, zero_add, mul_zero, zero_mul]
 try ring

theorem solution :
∀ (f : ℚ),
((leftSide f).coeff 8 = (rightSide f).coeff 8) ∧
((leftSide f).coeff 9 = (rightSide f).coeff 9) ∧
((leftSide f).coeff 10 = (rightSide f).coeff 10) ∧
((leftSide f).coeff 11 = (rightSide f).coeff 11) := by
 intro f
 exact ⟨coefficient_8 f, coefficient_9 f, coefficient_10 f, coefficient_11 f⟩
#print axioms solution
