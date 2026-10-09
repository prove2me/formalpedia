-- Prove2me | solution 1 for Helfgott.reciprocal_certificate_log_grid
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:52:39.710991+00:00
-- url     : https://prove2.me/submissions/b727cf78-7e8f-4644-b39b-d20dbb1bbcb4

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Real
open scoped BigOperators
namespace Helfgott

private lemma reciprocalLog94 : Real.log (12088 : ℝ) ≤ (94 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 12088)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 94 / 10) 70
  have hq : (12088 : ℚ) ≤ ∑ i ∈ Finset.range 70, (94 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (12088 : ℝ) ≤ ∑ i ∈ Finset.range 70, (94 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog95 : Real.log (13359 : ℝ) ≤ (95 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 13359)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 95 / 10) 70
  have hq : (13359 : ℚ) ≤ ∑ i ∈ Finset.range 70, (95 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (13359 : ℝ) ≤ ∑ i ∈ Finset.range 70, (95 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog96 : Real.log (14764 : ℝ) ≤ (96 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 14764)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 96 / 10) 70
  have hq : (14764 : ℚ) ≤ ∑ i ∈ Finset.range 70, (96 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (14764 : ℝ) ≤ ∑ i ∈ Finset.range 70, (96 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog97 : Real.log (16317 : ℝ) ≤ (97 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 16317)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 97 / 10) 70
  have hq : (16317 : ℚ) ≤ ∑ i ∈ Finset.range 70, (97 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (16317 : ℝ) ≤ ∑ i ∈ Finset.range 70, (97 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog98 : Real.log (18033 : ℝ) ≤ (98 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 18033)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 98 / 10) 70
  have hq : (18033 : ℚ) ≤ ∑ i ∈ Finset.range 70, (98 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (18033 : ℝ) ≤ ∑ i ∈ Finset.range 70, (98 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog99 : Real.log (19930 : ℝ) ≤ (99 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 19930)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 10) 70
  have hq : (19930 : ℚ) ≤ ∑ i ∈ Finset.range 70, (99 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (19930 : ℝ) ≤ ∑ i ∈ Finset.range 70, (99 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog100 : Real.log (22026 : ℝ) ≤ (100 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 22026)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 100 / 10) 70
  have hq : (22026 : ℚ) ≤ ∑ i ∈ Finset.range 70, (100 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (22026 : ℝ) ≤ ∑ i ∈ Finset.range 70, (100 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog101 : Real.log (24343 : ℝ) ≤ (101 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 24343)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 101 / 10) 70
  have hq : (24343 : ℚ) ≤ ∑ i ∈ Finset.range 70, (101 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (24343 : ℝ) ≤ ∑ i ∈ Finset.range 70, (101 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog102 : Real.log (26903 : ℝ) ≤ (102 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 26903)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 102 / 10) 70
  have hq : (26903 : ℚ) ≤ ∑ i ∈ Finset.range 70, (102 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (26903 : ℝ) ≤ ∑ i ∈ Finset.range 70, (102 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog103 : Real.log (29732 : ℝ) ≤ (103 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 29732)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 103 / 10) 70
  have hq : (29732 : ℚ) ≤ ∑ i ∈ Finset.range 70, (103 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (29732 : ℝ) ≤ ∑ i ∈ Finset.range 70, (103 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog104 : Real.log (32859 : ℝ) ≤ (104 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 32859)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 104 / 10) 70
  have hq : (32859 : ℚ) ≤ ∑ i ∈ Finset.range 70, (104 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (32859 : ℝ) ≤ ∑ i ∈ Finset.range 70, (104 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog105 : Real.log (36315 : ℝ) ≤ (105 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 36315)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 105 / 10) 70
  have hq : (36315 : ℚ) ≤ ∑ i ∈ Finset.range 70, (105 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (36315 : ℝ) ≤ ∑ i ∈ Finset.range 70, (105 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog106 : Real.log (40134 : ℝ) ≤ (106 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 40134)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 106 / 10) 70
  have hq : (40134 : ℚ) ≤ ∑ i ∈ Finset.range 70, (106 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (40134 : ℝ) ≤ ∑ i ∈ Finset.range 70, (106 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog107 : Real.log (44355 : ℝ) ≤ (107 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 44355)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 107 / 10) 70
  have hq : (44355 : ℚ) ≤ ∑ i ∈ Finset.range 70, (107 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (44355 : ℝ) ≤ ∑ i ∈ Finset.range 70, (107 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog108 : Real.log (49020 : ℝ) ≤ (108 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 49020)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 108 / 10) 70
  have hq : (49020 : ℚ) ≤ ∑ i ∈ Finset.range 70, (108 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (49020 : ℝ) ≤ ∑ i ∈ Finset.range 70, (108 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog109 : Real.log (54176 : ℝ) ≤ (109 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 54176)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 109 / 10) 70
  have hq : (54176 : ℚ) ≤ ∑ i ∈ Finset.range 70, (109 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (54176 : ℝ) ≤ ∑ i ∈ Finset.range 70, (109 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog110 : Real.log (59874 : ℝ) ≤ (110 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 59874)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 110 / 10) 70
  have hq : (59874 : ℚ) ≤ ∑ i ∈ Finset.range 70, (110 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (59874 : ℝ) ≤ ∑ i ∈ Finset.range 70, (110 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog111 : Real.log (66171 : ℝ) ≤ (111 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 66171)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 111 / 10) 70
  have hq : (66171 : ℚ) ≤ ∑ i ∈ Finset.range 70, (111 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (66171 : ℝ) ≤ ∑ i ∈ Finset.range 70, (111 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog112 : Real.log (73130 : ℝ) ≤ (112 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 73130)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 112 / 10) 70
  have hq : (73130 : ℚ) ≤ ∑ i ∈ Finset.range 70, (112 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (73130 : ℝ) ≤ ∑ i ∈ Finset.range 70, (112 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog113 : Real.log (80821 : ℝ) ≤ (113 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 80821)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 113 / 10) 70
  have hq : (80821 : ℚ) ≤ ∑ i ∈ Finset.range 70, (113 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (80821 : ℝ) ≤ ∑ i ∈ Finset.range 70, (113 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog114 : Real.log (89321 : ℝ) ≤ (114 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 89321)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 114 / 10) 70
  have hq : (89321 : ℚ) ≤ ∑ i ∈ Finset.range 70, (114 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (89321 : ℝ) ≤ ∑ i ∈ Finset.range 70, (114 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog115 : Real.log (98715 : ℝ) ≤ (115 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 98715)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 115 / 10) 70
  have hq : (98715 : ℚ) ≤ ∑ i ∈ Finset.range 70, (115 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (98715 : ℝ) ≤ ∑ i ∈ Finset.range 70, (115 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog116 : Real.log (109097 : ℝ) ≤ (116 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 109097)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 116 / 10) 70
  have hq : (109097 : ℚ) ≤ ∑ i ∈ Finset.range 70, (116 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (109097 : ℝ) ≤ ∑ i ∈ Finset.range 70, (116 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog117 : Real.log (120571 : ℝ) ≤ (117 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 120571)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 117 / 10) 70
  have hq : (120571 : ℚ) ≤ ∑ i ∈ Finset.range 70, (117 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (120571 : ℝ) ≤ ∑ i ∈ Finset.range 70, (117 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog118 : Real.log (133252 : ℝ) ≤ (118 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 133252)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 118 / 10) 70
  have hq : (133252 : ℚ) ≤ ∑ i ∈ Finset.range 70, (118 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (133252 : ℝ) ≤ ∑ i ∈ Finset.range 70, (118 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog119 : Real.log (147266 : ℝ) ≤ (119 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 147266)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 119 / 10) 70
  have hq : (147266 : ℚ) ≤ ∑ i ∈ Finset.range 70, (119 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (147266 : ℝ) ≤ ∑ i ∈ Finset.range 70, (119 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog120 : Real.log (162754 : ℝ) ≤ (120 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 162754)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 120 / 10) 70
  have hq : (162754 : ℚ) ≤ ∑ i ∈ Finset.range 70, (120 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (162754 : ℝ) ≤ ∑ i ∈ Finset.range 70, (120 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog121 : Real.log (179871 : ℝ) ≤ (121 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 179871)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 121 / 10) 70
  have hq : (179871 : ℚ) ≤ ∑ i ∈ Finset.range 70, (121 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (179871 : ℝ) ≤ ∑ i ∈ Finset.range 70, (121 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog122 : Real.log (198789 : ℝ) ≤ (122 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 198789)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 122 / 10) 70
  have hq : (198789 : ℚ) ≤ ∑ i ∈ Finset.range 70, (122 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (198789 : ℝ) ≤ ∑ i ∈ Finset.range 70, (122 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog123 : Real.log (219695 : ℝ) ≤ (123 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 219695)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 123 / 10) 70
  have hq : (219695 : ℚ) ≤ ∑ i ∈ Finset.range 70, (123 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (219695 : ℝ) ≤ ∑ i ∈ Finset.range 70, (123 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog124 : Real.log (242801 : ℝ) ≤ (124 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 242801)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 124 / 10) 70
  have hq : (242801 : ℚ) ≤ ∑ i ∈ Finset.range 70, (124 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (242801 : ℝ) ≤ ∑ i ∈ Finset.range 70, (124 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog125 : Real.log (268337 : ℝ) ≤ (125 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 268337)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 125 / 10) 70
  have hq : (268337 : ℚ) ≤ ∑ i ∈ Finset.range 70, (125 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (268337 : ℝ) ≤ ∑ i ∈ Finset.range 70, (125 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog126 : Real.log (296558 : ℝ) ≤ (126 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 296558)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 126 / 10) 70
  have hq : (296558 : ℚ) ≤ ∑ i ∈ Finset.range 70, (126 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (296558 : ℝ) ≤ ∑ i ∈ Finset.range 70, (126 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog127 : Real.log (327747 : ℝ) ≤ (127 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 327747)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 127 / 10) 70
  have hq : (327747 : ℚ) ≤ ∑ i ∈ Finset.range 70, (127 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (327747 : ℝ) ≤ ∑ i ∈ Finset.range 70, (127 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog128 : Real.log (362217 : ℝ) ≤ (128 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 362217)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 128 / 10) 70
  have hq : (362217 : ℚ) ≤ ∑ i ∈ Finset.range 70, (128 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (362217 : ℝ) ≤ ∑ i ∈ Finset.range 70, (128 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog129 : Real.log (400312 : ℝ) ≤ (129 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 400312)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 129 / 10) 70
  have hq : (400312 : ℚ) ≤ ∑ i ∈ Finset.range 70, (129 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (400312 : ℝ) ≤ ∑ i ∈ Finset.range 70, (129 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog130 : Real.log (442413 : ℝ) ≤ (130 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 442413)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 130 / 10) 70
  have hq : (442413 : ℚ) ≤ ∑ i ∈ Finset.range 70, (130 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (442413 : ℝ) ≤ ∑ i ∈ Finset.range 70, (130 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog131 : Real.log (488942 : ℝ) ≤ (131 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 488942)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 131 / 10) 70
  have hq : (488942 : ℚ) ≤ ∑ i ∈ Finset.range 70, (131 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (488942 : ℝ) ≤ ∑ i ∈ Finset.range 70, (131 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog132 : Real.log (540364 : ℝ) ≤ (132 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 540364)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 132 / 10) 70
  have hq : (540364 : ℚ) ≤ ∑ i ∈ Finset.range 70, (132 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (540364 : ℝ) ≤ ∑ i ∈ Finset.range 70, (132 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog133 : Real.log (597195 : ℝ) ≤ (133 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 597195)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 133 / 10) 70
  have hq : (597195 : ℚ) ≤ ∑ i ∈ Finset.range 70, (133 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (597195 : ℝ) ≤ ∑ i ∈ Finset.range 70, (133 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog134 : Real.log (660003 : ℝ) ≤ (134 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 660003)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 134 / 10) 70
  have hq : (660003 : ℚ) ≤ ∑ i ∈ Finset.range 70, (134 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (660003 : ℝ) ≤ ∑ i ∈ Finset.range 70, (134 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog135 : Real.log (729416 : ℝ) ≤ (135 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 729416)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 135 / 10) 70
  have hq : (729416 : ℚ) ≤ ∑ i ∈ Finset.range 70, (135 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (729416 : ℝ) ≤ ∑ i ∈ Finset.range 70, (135 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog136 : Real.log (806129 : ℝ) ≤ (136 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 806129)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 136 / 10) 70
  have hq : (806129 : ℚ) ≤ ∑ i ∈ Finset.range 70, (136 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (806129 : ℝ) ≤ ∑ i ∈ Finset.range 70, (136 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog137 : Real.log (890911 : ℝ) ≤ (137 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 890911)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 137 / 10) 70
  have hq : (890911 : ℚ) ≤ ∑ i ∈ Finset.range 70, (137 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (890911 : ℝ) ≤ ∑ i ∈ Finset.range 70, (137 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog138 : Real.log (984609 : ℝ) ≤ (138 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 984609)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 138 / 10) 70
  have hq : (984609 : ℚ) ≤ ∑ i ∈ Finset.range 70, (138 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (984609 : ℝ) ≤ ∑ i ∈ Finset.range 70, (138 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog139 : Real.log (1088161 : ℝ) ≤ (139 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1088161)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 139 / 10) 70
  have hq : (1088161 : ℚ) ≤ ∑ i ∈ Finset.range 70, (139 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (1088161 : ℝ) ≤ ∑ i ∈ Finset.range 70, (139 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

private lemma reciprocalLog140 : Real.log (1202604 : ℝ) ≤ (140 : ℝ) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1202604)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 140 / 10) 70
  have hq : (1202604 : ℚ) ≤ ∑ i ∈ Finset.range 70, (140 / 10 : ℚ) ^ i / (Nat.factorial i : ℚ) := by
    decide +kernel
  have hr : (1202604 : ℝ) ≤ ∑ i ∈ Finset.range 70, (140 / 10 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    exact hc
  exact hr.trans he

theorem reciprocal_certificate_log_grid_complete : ∀ c ∈ ([(94, 12088), (95, 13359), (96, 14764), (97, 16317), (98, 18033), (99, 19930), (100, 22026), (101, 24343), (102, 26903), (103, 29732), (104, 32859), (105, 36315), (106, 40134), (107, 44355), (108, 49020), (109, 54176), (110, 59874), (111, 66171), (112, 73130), (113, 80821), (114, 89321), (115, 98715), (116, 109097), (117, 120571), (118, 133252), (119, 147266), (120, 162754), (121, 179871), (122, 198789), (123, 219695), (124, 242801), (125, 268337), (126, 296558), (127, 327747), (128, 362217), (129, 400312), (130, 442413), (131, 488942), (132, 540364), (133, 597195), (134, 660003), (135, 729416), (136, 806129), (137, 890911), (138, 984609), (139, 1088161), (140, 1202604)] : List (ℕ × ℕ)), Real.log (c.2 : ℝ) ≤ (c.1 : ℝ) / 10 := by
  simp only [List.forall_mem_cons]
  exact ⟨reciprocalLog94, reciprocalLog95, reciprocalLog96, reciprocalLog97, reciprocalLog98, reciprocalLog99, reciprocalLog100, reciprocalLog101, reciprocalLog102, reciprocalLog103, reciprocalLog104, reciprocalLog105, reciprocalLog106, reciprocalLog107, reciprocalLog108, reciprocalLog109, reciprocalLog110, reciprocalLog111, reciprocalLog112, reciprocalLog113, reciprocalLog114, reciprocalLog115, reciprocalLog116, reciprocalLog117, reciprocalLog118, reciprocalLog119, reciprocalLog120, reciprocalLog121, reciprocalLog122, reciprocalLog123, reciprocalLog124, reciprocalLog125, reciprocalLog126, reciprocalLog127, reciprocalLog128, reciprocalLog129, reciprocalLog130, reciprocalLog131, reciprocalLog132, reciprocalLog133, reciprocalLog134, reciprocalLog135, reciprocalLog136, reciprocalLog137, reciprocalLog138, reciprocalLog139, reciprocalLog140, List.forall_mem_nil _⟩

end Helfgott

open Helfgott
theorem solution : ∀ c ∈ ([(94, 12088), (95, 13359), (96, 14764), (97, 16317), (98, 18033), (99, 19930), (100, 22026), (101, 24343), (102, 26903), (103, 29732), (104, 32859), (105, 36315), (106, 40134), (107, 44355), (108, 49020), (109, 54176), (110, 59874), (111, 66171), (112, 73130), (113, 80821), (114, 89321), (115, 98715), (116, 109097), (117, 120571), (118, 133252), (119, 147266), (120, 162754), (121, 179871), (122, 198789), (123, 219695), (124, 242801), (125, 268337), (126, 296558), (127, 327747), (128, 362217), (129, 400312), (130, 442413), (131, 488942), (132, 540364), (133, 597195), (134, 660003), (135, 729416), (136, 806129), (137, 890911), (138, 984609), (139, 1088161), (140, 1202604)] : List (ℕ × ℕ)), Real.log (c.2 : ℝ) ≤ (c.1 : ℝ) / 10 := Helfgott.reciprocal_certificate_log_grid_complete
#print axioms solution
