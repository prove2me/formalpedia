-- Prove2me | solution 1 for GeneralPieces.Series.cfM_toM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:33:35.058233+00:00
-- url     : https://prove2.me/submissions/4c25db24-7715-48b3-815c-42e899cb624b

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
import Theorems.Thm_GeneralPieces_Series_toM_single
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
theorem _root_.solution (F : L) (x y : ℤ) : cfM (toM F) x y = F.coeff (x, y) := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp [cfM]
  | add f g hf hg =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← hf, ← hg]
    rfl
  | single p r =>
    obtain ⟨a, b⟩ := p
    rw [toM_single, cfM, cf_smul, cf_mo, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : y = b ∧ x = a
    · rw [if_pos h, if_pos (by rw [h.1, h.2]), mul_one]
    · rw [if_neg h, if_neg (fun g => h ⟨(congrArg Prod.snd g).symm, (congrArg Prod.fst g).symm⟩), mul_zero]
end GeneralPieces.Series
