-- Prove2me | solution 1 for GeneralPieces.Between.between_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:46:35.03076+00:00
-- url     : https://prove2.me/submissions/22fcd27b-3313-4522-a9ac-7ac7b5bbde37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_Num_Between
import Theorems.Thm_GeneralPieces_Between_half_pow_even

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Between
open Groundwork PaddedDescent.F Levels.Gen
namespace GeneralPieces.Between
theorem _root_.solution (l : ℕ) : 0.85 * (1 / Real.sqrt 2) ^ l ≤ (num l : ℝ) / (den l : ℝ) ∧ (num l : ℝ) / (den l : ℝ) ≤ (1 / Real.sqrt 2) ^ l := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
  · have h1 : num (2 * j) = 5 := by unfold num; omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    have h3 : (0 : ℝ) < 1 / 2 ^ j := by positivity
    have h4 : ((5 : ℕ) : ℝ) / ((5 * 2 ^ j : ℕ) : ℝ) = 1 / 2 ^ j := by push_cast; field_simp
    rw [h1, den, h2, half_pow_even, h4]
    exact ⟨by linarith, le_rfl⟩
  · have h1 : num (2 * j + 1) = 7 := by unfold num; omega
    have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    have h3 : (0 : ℝ) < 1 / 2 ^ j := by positivity
    have h4 : ((7 : ℕ) : ℝ) / ((5 * 2 ^ (j + 1) : ℕ) : ℝ) = 1 / 2 ^ j * (7 / 10) := by push_cast; rw [pow_succ]; field_simp; norm_num
    have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h5 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by field_simp; linarith
    rw [h1, den, h2, pow_succ, half_pow_even, h4, h5]
    generalize Real.sqrt 2 = s at *
    have hs1 : 7 / 5 ≤ s := by
      by_contra h
      have h' : s < 7 / 5 := not_le.1 h
      nlinarith
    have hs3 : 0.85 * s ≤ 7 / 5 := by
      by_contra h
      have h' : 7 / 5 < 0.85 * s := not_le.1 h
      nlinarith
    constructor
    · have := mul_le_mul_of_nonneg_left hs3 h3.le
      linarith
    · have := mul_le_mul_of_nonneg_left hs1 h3.le
      linarith
end GeneralPieces.Between
