-- Prove2me | solution 1 for GeneralPieces.Series.cf_mo_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:37:52.537301+00:00
-- url     : https://prove2.me/submissions/ba3ae12a-7180-413e-a483-70ab3a8ee34e

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

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (a b : ℤ) (f : S) (x y : ℤ) : cf (mo a b * f) x y = cf f (x - a) (y - b) := by
  unfold cf mo
  rw [HahnSeries.coeff_single_mul, T, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (x - a) (fun m _ => by constructor <;> intro h <;> omega), one_mul]
end GeneralPieces.Series
