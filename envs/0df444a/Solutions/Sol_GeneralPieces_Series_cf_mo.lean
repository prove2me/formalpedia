-- Prove2me | solution 1 for GeneralPieces.Series.cf_mo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:37:51.340128+00:00
-- url     : https://prove2.me/submissions/0715e7a2-b4b5-4c34-a344-097b019d3632

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Definitions.Def_GeneralPieces_Series_Rings
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_smul
attribute [local simp] GeneralPieces.Series.cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (a b x y : ℤ) : cf (mo a b) x y = if x = a ∧ y = b then 1 else 0 := by
  unfold cf mo
  by_cases hy : y = b
  · subst hy
    simp [eq_comm]
  · rw [HahnSeries.coeff_single_of_ne hy]
    simp [hy]
end GeneralPieces.Series
