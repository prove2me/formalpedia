-- Prove2me | solution 1 for GeneralPieces.Series.cfP_dW_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:09:18.737979+00:00
-- url     : https://prove2.me/submissions/67fe8ede-6490-47d5-be45-a79f0332f126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_dW_pow
import Theorems.Thm_GeneralPieces_Series_cf_mo_mul
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sum
import Theorems.Thm_GeneralPieces_Series_toP_W
attribute [local simp] GeneralPieces.Series.cf_smul



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
namespace GeneralPieces.Series
theorem _root_.solution (H : ℕ) (f : Lp) (x y : ℤ) :
    cfP (toP dW ^ H * f) x y = ∑ i ∈ range (H + 1), ((-1) ^ i * (H.choose i : ℚ)) * cfP f (x - (H - i)) (y - i) := by
  rw [← map_pow, dW_pow, map_sum, sum_mul, cfP, cf_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, toP_W, smul_mul_assoc, cf_smul, cf_mo_mul, cfP]
end GeneralPieces.Series
