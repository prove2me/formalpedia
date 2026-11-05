-- Prove2me | solution 1 for GeneralPieces.Series.dv_iter_ser
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:36:27.456907+00:00
-- url     : https://prove2.me/submissions/9946694d-5c45-4eef-996e-b6b0d7bd8a05

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_ser_congr
import Theorems.Thm_GeneralPieces_Series_dv_ser
import Theorems.Thm_ClauseBound_Boson_Scalars_succ_mul_choose
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
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (b p q : ℕ) (c : ℤ → ℚ) :
    dv^[b] (ser p q c) = ser p (q + b) fun k => (b.factorial : ℚ) * (Ring.choose (k - (q : ℤ)) b : ℤ) * c k := by
  induction b generalizing q c with
  | zero => exact ser_congr _ _ fun k => by simp
  | succ b ih =>
    rw [Function.iterate_succ_apply, dv_ser, ih, show q + 1 + b = q + (b + 1) by omega]
    refine ser_congr _ _ fun k => ?_
    have e := congrArg (Int.cast : ℤ → ℚ) (ClauseBound.Boson.Scalars.succ_mul_choose (k - (q : ℤ)) b)
    push_cast at e
    rw [Nat.factorial_succ, show k - ((q + 1 : ℕ) : ℤ) = k - (q : ℤ) - 1 by push_cast; ring]
    push_cast
    linear_combination (-(b.factorial : ℚ) * c k) * e
end GeneralPieces.Series
