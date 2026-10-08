-- Prove2me | solution 1 for MazurTransfer.order27_nsq_complete_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T17:11:33.156998+00:00
-- url     : https://prove2.me/submissions/394b966d-1c8e-4cca-b7a9-d017df1eefa3

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Theorems.Thm_MazurTransfer_order27_nsq_block_0_3
import Theorems.Thm_MazurTransfer_order27_nsq_block_4_7
import Theorems.Thm_MazurTransfer_order27_nsq_block_8_11
import Theorems.Thm_MazurTransfer_order27_nsq_block_12_15
import Theorems.Thm_MazurTransfer_order27_nsq_block_16_18
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27NSqPolynomialData
open Polynomial
namespace MazurTransfer.Order27NSqPolynomial

theorem degree_p_tlN0 (f : ℚ) : (p_tlN0 f).natDegree ≤ 4 := by
 unfold p_tlN0
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlN1 (f : ℚ) : (p_tlN1 f).natDegree ≤ 6 := by
 unfold p_tlN1
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlN2 (f : ℚ) : (p_tlN2 f).natDegree ≤ 7 := by
 unfold p_tlN2
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlN3 (f : ℚ) : (p_tlN3 f).natDegree ≤ 9 := by
 unfold p_tlN3
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

theorem degree_p_tlNSqP3c0 (f : ℚ) : (p_tlNSqP3c0 f).natDegree ≤ 4 := by
 unfold p_tlNSqP3c0
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlNSqP3c1 (f : ℚ) : (p_tlNSqP3c1 f).natDegree ≤ 6 := by
 unfold p_tlNSqP3c1
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlNSqP3c2 (f : ℚ) : (p_tlNSqP3c2 f).natDegree ≤ 7 := by
 unfold p_tlNSqP3c2
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlNSqP3c3 (f : ℚ) : (p_tlNSqP3c3 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c3
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c4 (f : ℚ) : (p_tlNSqP3c4 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c4
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c5 (f : ℚ) : (p_tlNSqP3c5 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c5
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c6 (f : ℚ) : (p_tlNSqP3c6 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c6
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c7 (f : ℚ) : (p_tlNSqP3c7 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c7
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c8 (f : ℚ) : (p_tlNSqP3c8 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c8
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c9 (f : ℚ) : (p_tlNSqP3c9 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c9
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c10 (f : ℚ) : (p_tlNSqP3c10 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c10
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqP3c11 (f : ℚ) : (p_tlNSqP3c11 f).natDegree ≤ 8 := by
 unfold p_tlNSqP3c11
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlNSqQ3c0 (f : ℚ) : (p_tlNSqQ3c0 f).natDegree ≤ 3 := by
 unfold p_tlNSqQ3c0
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))

theorem degree_p_tlNSqQ3c1 (f : ℚ) : (p_tlNSqQ3c1 f).natDegree ≤ 5 := by
 unfold p_tlNSqQ3c1
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlNSqQ3c2 (f : ℚ) : (p_tlNSqQ3c2 f).natDegree ≤ 6 := by
 unfold p_tlNSqQ3c2
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlNSqQ3c3 (f : ℚ) : (p_tlNSqQ3c3 f).natDegree ≤ 7 := by
 unfold p_tlNSqQ3c3
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem degree_p_tlNSqQ3c4 (f : ℚ) : (p_tlNSqQ3c4 f).natDegree ≤ 8 := by
 unfold p_tlNSqQ3c4
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))))))

theorem degree_p_tlNSqQ3c5 (f : ℚ) : (p_tlNSqQ3c5 f).natDegree ≤ 9 := by
 unfold p_tlNSqQ3c5
 exact (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) (Polynomial.natDegree_add_le_of_degree_le ((Polynomial.natDegree_monomial_le _).trans (by norm_num)) ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))))

theorem left_degree (f : ℚ) : (leftSide f).natDegree ≤ 18 := by
 unfold leftSide
 exact Polynomial.natDegree_mul_le_of_le (degree_p_tlN3 f) <|
  Polynomial.natDegree_add_le_of_degree_le
   (Polynomial.natDegree_add_le_of_degree_le
    (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlN0 f).trans (by norm_num))
      ((degree_p_tlN1 f).trans (by norm_num)))
    ((degree_p_tlN2 f).trans (by norm_num))) (degree_p_tlN3 f)

theorem right_degree (f : ℚ) : (rightSide f).natDegree ≤ 18 := by
 unfold rightSide
 exact Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlNSqP3c0 f).trans (by norm_num)) ((degree_p_tlNSqP3c1 f).trans (by norm_num))) ((degree_p_tlNSqP3c2 f).trans (by norm_num))) ((degree_p_tlNSqP3c3 f).trans (by norm_num))) ((degree_p_tlNSqP3c4 f).trans (by norm_num))) ((degree_p_tlNSqP3c5 f).trans (by norm_num))) ((degree_p_tlNSqP3c6 f).trans (by norm_num))) ((degree_p_tlNSqP3c7 f).trans (by norm_num))) ((degree_p_tlNSqP3c8 f).trans (by norm_num))) ((degree_p_tlNSqP3c9 f).trans (by norm_num))) ((degree_p_tlNSqP3c10 f).trans (by norm_num))) ((degree_p_tlNSqP3c11 f).trans (by norm_num))) (Polynomial.natDegree_mul_le_of_le (m := 9) (n := 9) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlNSqQ3c0 f).trans (by norm_num)) ((degree_p_tlNSqQ3c1 f).trans (by norm_num))) ((degree_p_tlNSqQ3c2 f).trans (by norm_num))) ((degree_p_tlNSqQ3c3 f).trans (by norm_num))) ((degree_p_tlNSqQ3c4 f).trans (by norm_num))) ((degree_p_tlNSqQ3c5 f).trans (by norm_num))) (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le ((degree_p_tlT0 f).trans (by norm_num)) ((degree_p_tlT1 f).trans (by norm_num))) ((degree_p_tlT2 f).trans (by norm_num))) ((degree_p_tlT3 f).trans (by norm_num))))

end MazurTransfer.Order27NSqPolynomial
#print axioms MazurTransfer.Order27NSqPolynomial.right_degree

open Polynomial MazurTransfer.Order27NSqPolynomial
theorem solution :
∀ (f : ℚ), leftSide f = rightSide f := by
 intro f
 apply (Polynomial.ext_iff_natDegree_le (left_degree f) (right_degree f)).2
 intro n hn
 interval_cases n
 · exact (MazurTransfer.order27_nsq_block_0_3 f).1
 · exact (MazurTransfer.order27_nsq_block_0_3 f).2.1
 · exact (MazurTransfer.order27_nsq_block_0_3 f).2.2.1
 · exact (MazurTransfer.order27_nsq_block_0_3 f).2.2.2
 · exact (MazurTransfer.order27_nsq_block_4_7 f).1
 · exact (MazurTransfer.order27_nsq_block_4_7 f).2.1
 · exact (MazurTransfer.order27_nsq_block_4_7 f).2.2.1
 · exact (MazurTransfer.order27_nsq_block_4_7 f).2.2.2
 · exact (MazurTransfer.order27_nsq_block_8_11 f).1
 · exact (MazurTransfer.order27_nsq_block_8_11 f).2.1
 · exact (MazurTransfer.order27_nsq_block_8_11 f).2.2.1
 · exact (MazurTransfer.order27_nsq_block_8_11 f).2.2.2
 · exact (MazurTransfer.order27_nsq_block_12_15 f).1
 · exact (MazurTransfer.order27_nsq_block_12_15 f).2.1
 · exact (MazurTransfer.order27_nsq_block_12_15 f).2.2.1
 · exact (MazurTransfer.order27_nsq_block_12_15 f).2.2.2
 · exact (MazurTransfer.order27_nsq_block_16_18 f).1
 · exact (MazurTransfer.order27_nsq_block_16_18 f).2.1
 · exact (MazurTransfer.order27_nsq_block_16_18 f).2.2

#print axioms solution
