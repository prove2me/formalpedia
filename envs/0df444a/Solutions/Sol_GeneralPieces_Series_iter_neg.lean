-- Prove2me | solution 1 for GeneralPieces.Series.iter_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:34:38.960437+00:00
-- url     : https://prove2.me/submissions/2ac1e477-07f7-492d-823a-7b9a373e1e07

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_iter_smul
import Theorems.Thm_GeneralPieces_Series_deriv_pow
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
variable {A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.Series
theorem _root_.solution (D : Derivation ℚ A A) {ε : A} (h : D ε = -ε ^ 2) (a m : ℕ) :
    D^[a] (ε ^ m) = ((a.factorial : ℚ) * (Ring.choose (-(m : ℤ)) a : ℤ)) • ε ^ (m + a) := by
  induction a generalizing m with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, deriv_pow D (s := -1) (by rw [neg_one_smul, h]), iter_smul, ih (m + 1), smul_smul,
      show m + 1 + a = m + (a + 1) by omega]
    congr 1
    have e := congrArg (Int.cast : ℤ → ℚ) (ClauseBound.Boson.Scalars.succ_mul_choose (-(m : ℤ)) a)
    push_cast at e
    rw [Nat.factorial_succ]
    push_cast
    rw [show (-((m : ℤ) + 1)) = -(m : ℤ) - 1 by ring]
    linear_combination (a.factorial : ℚ) * (-e)
end GeneralPieces.Series
