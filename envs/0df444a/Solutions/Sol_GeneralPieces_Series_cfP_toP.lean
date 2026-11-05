-- Prove2me | solution 1 for GeneralPieces.Series.cfP_toP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:24:55.040075+00:00
-- url     : https://prove2.me/submissions/435d523d-2269-49e8-8560-59d6c50a9575

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
import Theorems.Thm_GeneralPieces_Series_cf_mo
import Theorems.Thm_GeneralPieces_Series_toP_single
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
theorem _root_.solution (F : L) (x y : ℤ) : cfP (toP F) x y = F.coeff (x, y) := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp [cfP]
  | add f g hf hg =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← hf, ← hg]
    rfl
  | single p r =>
    obtain ⟨a, b⟩ := p
    rw [toP_single, cfP, cf_smul, cf_mo, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : x = a ∧ y = b
    · rw [if_pos h, if_pos (by rw [h.1, h.2]), mul_one]
    · rw [if_neg h, if_neg (fun g => h ⟨(congrArg Prod.fst g).symm, (congrArg Prod.snd g).symm⟩), mul_zero]
end GeneralPieces.Series
