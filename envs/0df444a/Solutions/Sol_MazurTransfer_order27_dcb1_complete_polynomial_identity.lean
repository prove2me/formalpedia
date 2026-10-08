-- Prove2me | solution 1 for MazurTransfer.order27_dcb1_complete_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:35:39.626046+00:00
-- url     : https://prove2.me/submissions/17eed14d-f46b-4eaa-a9d4-a97f5fc961a9

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Theorems.Thm_MazurTransfer_order27_dcb1_block_0_3
import Theorems.Thm_MazurTransfer_order27_dcb1_block_4_7
import Theorems.Thm_MazurTransfer_order27_dcb1_block_8_11
import Theorems.Thm_MazurTransfer_order27_dcb1_block_12_15
import Theorems.Thm_MazurTransfer_order27_dcb1_block_16_16
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27DCb1PolynomialData
namespace MazurTransfer.Order27DCb1Polynomial
open Polynomial

theorem degree_p_tlDSqP0c3 (f : ℚ) : (p_tlDSqP0c3 f).natDegree ≤ 8 := by
 unfold p_tlDSqP0c3
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDSqP0c4 (f : ℚ) : (p_tlDSqP0c4 f).natDegree ≤ 8 := by
 unfold p_tlDSqP0c4
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDSqP0c5 (f : ℚ) : (p_tlDSqP0c5 f).natDegree ≤ 8 := by
 unfold p_tlDSqP0c5
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlD0 (f : ℚ) : (p_tlD0 f).natDegree ≤ 6 := by
 unfold p_tlD0
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlD1 (f : ℚ) : (p_tlD1 f).natDegree ≤ 8 := by
 unfold p_tlD1
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlT0 (f : ℚ) : (p_tlT0 f).natDegree ≤ 4 := by
 unfold p_tlT0
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlT1 (f : ℚ) : (p_tlT1 f).natDegree ≤ 6 := by
 unfold p_tlT1
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlT2 (f : ℚ) : (p_tlT2 f).natDegree ≤ 7 := by
 unfold p_tlT2
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlT3 (f : ℚ) : (p_tlT3 f).natDegree ≤ 9 := by
 unfold p_tlT3
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))

theorem degree_p_tlDCbP1c0 (f : ℚ) : (p_tlDCbP1c0 f).natDegree ≤ 4 := by
 unfold p_tlDCbP1c0
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbP1c1 (f : ℚ) : (p_tlDCbP1c1 f).natDegree ≤ 6 := by
 unfold p_tlDCbP1c1
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbP1c2 (f : ℚ) : (p_tlDCbP1c2 f).natDegree ≤ 7 := by
 unfold p_tlDCbP1c2
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbP1c3 (f : ℚ) : (p_tlDCbP1c3 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c3
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c4 (f : ℚ) : (p_tlDCbP1c4 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c4
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c5 (f : ℚ) : (p_tlDCbP1c5 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c5
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c6 (f : ℚ) : (p_tlDCbP1c6 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c6
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c7 (f : ℚ) : (p_tlDCbP1c7 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c7
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c8 (f : ℚ) : (p_tlDCbP1c8 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c8
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c9 (f : ℚ) : (p_tlDCbP1c9 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c9
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c10 (f : ℚ) : (p_tlDCbP1c10 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c10
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c11 (f : ℚ) : (p_tlDCbP1c11 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c11
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlDCbP1c12 (f : ℚ) : (p_tlDCbP1c12 f).natDegree ≤ 8 := by
 unfold p_tlDCbP1c12
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbQ1c0 (f : ℚ) : (p_tlDCbQ1c0 f).natDegree ≤ 3 := by
 unfold p_tlDCbQ1c0
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))

theorem degree_p_tlDCbQ1c1 (f : ℚ) : (p_tlDCbQ1c1 f).natDegree ≤ 5 := by
 unfold p_tlDCbQ1c1
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbQ1c2 (f : ℚ) : (p_tlDCbQ1c2 f).natDegree ≤ 6 := by
 unfold p_tlDCbQ1c2
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbQ1c3 (f : ℚ) : (p_tlDCbQ1c3 f).natDegree ≤ 7 := by
 unfold p_tlDCbQ1c3
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbQ1c4 (f : ℚ) : (p_tlDCbQ1c4 f).natDegree ≤ 7 := by
 unfold p_tlDCbQ1c4
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlDCbQ1c5 (f : ℚ) : (p_tlDCbQ1c5 f).natDegree ≤ 7 := by
 unfold p_tlDCbQ1c5
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem left_degree (f : ℚ) : (leftSide f).natDegree ≤ 16 := by
 unfold leftSide
 exact (Polynomial.natDegree_mul_le_of_le (m := 8) (n := 8) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDSqP0c3 f).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDSqP0c4 f).trans (by norm_num)) ((degree_p_tlDSqP0c5 f).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlD0 f).trans (by norm_num)) ((degree_p_tlD1 f).trans (by norm_num)))).trans (by norm_num)

theorem right_degree (f : ℚ) : (rightSide f).natDegree ≤ 16 := by
 unfold rightSide
 exact Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c0 f).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c1 f).trans (by norm_num)) ((degree_p_tlDCbP1c2 f).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c3 f).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c4 f).trans (by norm_num)) ((degree_p_tlDCbP1c5 f).trans (by norm_num))))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c6 f).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c7 f).trans (by norm_num)) ((degree_p_tlDCbP1c8 f).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c9 f).trans (by norm_num)) ((degree_p_tlDCbP1c10 f).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbP1c11 f).trans (by norm_num)) ((degree_p_tlDCbP1c12 f).trans (by norm_num)))))) ((Polynomial.natDegree_mul_le_of_le (m := 7) (n := 9) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbQ1c0 f).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbQ1c1 f).trans (by norm_num)) ((degree_p_tlDCbQ1c2 f).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbQ1c3 f).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlDCbQ1c4 f).trans (by norm_num)) ((degree_p_tlDCbQ1c5 f).trans (by norm_num))))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlT0 f).trans (by norm_num)) ((degree_p_tlT1 f).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlT2 f).trans (by norm_num)) ((degree_p_tlT3 f).trans (by norm_num))))).trans (by norm_num))

end MazurTransfer.Order27DCb1Polynomial

#print axioms MazurTransfer.Order27DCb1Polynomial.right_degree

open Polynomial MazurTransfer.Order27DCb1Polynomial

theorem solution :
∀ (f : ℚ), leftSide f = rightSide f := by
 intro f
 apply (Polynomial.ext_iff_natDegree_le (left_degree f) (right_degree f)).2
 intro n hn
 interval_cases n
 · exact (MazurTransfer.order27_dcb1_block_0_3 f).1
 · exact (MazurTransfer.order27_dcb1_block_0_3 f).2.1
 · exact (MazurTransfer.order27_dcb1_block_0_3 f).2.2.1
 · exact (MazurTransfer.order27_dcb1_block_0_3 f).2.2.2
 · exact (MazurTransfer.order27_dcb1_block_4_7 f).1
 · exact (MazurTransfer.order27_dcb1_block_4_7 f).2.1
 · exact (MazurTransfer.order27_dcb1_block_4_7 f).2.2.1
 · exact (MazurTransfer.order27_dcb1_block_4_7 f).2.2.2
 · exact (MazurTransfer.order27_dcb1_block_8_11 f).1
 · exact (MazurTransfer.order27_dcb1_block_8_11 f).2.1
 · exact (MazurTransfer.order27_dcb1_block_8_11 f).2.2.1
 · exact (MazurTransfer.order27_dcb1_block_8_11 f).2.2.2
 · exact (MazurTransfer.order27_dcb1_block_12_15 f).1
 · exact (MazurTransfer.order27_dcb1_block_12_15 f).2.1
 · exact (MazurTransfer.order27_dcb1_block_12_15 f).2.2.1
 · exact (MazurTransfer.order27_dcb1_block_12_15 f).2.2.2
 · exact (MazurTransfer.order27_dcb1_block_16_16 f)

#print axioms solution
