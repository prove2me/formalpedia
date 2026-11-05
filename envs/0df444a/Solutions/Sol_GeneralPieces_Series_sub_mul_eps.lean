-- Prove2me | solution 1 for GeneralPieces.Series.sub_mul_eps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:24:52.848066+00:00
-- url     : https://prove2.me/submissions/cb9627ae-99ca-4e17-846a-28cfab5eb4ca

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
import Theorems.Thm_GeneralPieces_Series_ext_cf
import Theorems.Thm_GeneralPieces_Series_cf_diag
import Theorems.Thm_GeneralPieces_Series_cf_sub_mul
import Theorems.Thm_GeneralPieces_Series_cf_one

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution : (mo 1 0 - mo 0 1) * eps = 1 := by
  refine ext_cf fun x y => ?_
  rw [cf_sub_mul, eps, cf_diag, cf_diag, cf_one]
  split_ifs <;> first | rfl | omega | norm_num
end GeneralPieces.Series
