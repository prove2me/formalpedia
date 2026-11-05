-- Prove2me | solution 1 for GeneralPieces.Series.dW_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:08:03.970887+00:00
-- url     : https://prove2.me/submissions/e41e154d-ab0b-4d64-8414-1a32ab16e37a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_W_mul_W
import Theorems.Thm_GeneralPieces_Series_W_pow
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
namespace GeneralPieces.Series
theorem _root_.solution (H : ℕ) : dW ^ H = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) • W (H - i) i := by
  rw [dW, sub_eq_neg_add, add_pow]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ H := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [neg_pow, W_pow, W_pow, mul_assoc ((-1 : L) ^ i), W_mul_W, Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast, Nat.cast_sub hi']
  simp only [mul_zero, mul_one, zero_add, add_zero]
  ring
end GeneralPieces.Series
