-- Prove2me | solution 1 for GeneralPieces.Series.cf_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:08.649955+00:00
-- url     : https://prove2.me/submissions/577d0370-a778-40e2-aba1-1cc7493cbdc3

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
theorem _root_.solution (d : ℤ) (c : ℤ → ℚ) (j₀ x y : ℤ) : cf (diag d c j₀) x y = if j₀ ≤ y ∧ x + y = d then c y else 0 := by
  unfold cf diag
  rw [HahnSeries.coeff_ofSuppBddBelow]
  by_cases h : j₀ ≤ y
  · rw [if_pos h, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h2 : x + y = d
    · rw [if_pos (by omega), if_pos ⟨h, h2⟩]
    · rw [if_neg (by omega), if_neg (fun g => h2 g.2)]
  · rw [if_neg h, if_neg (fun g => h g.1)]
    rfl
end GeneralPieces.Series
