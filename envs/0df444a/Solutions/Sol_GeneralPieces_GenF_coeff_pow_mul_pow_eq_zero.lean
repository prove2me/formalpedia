-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_pow_mul_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:36:28.457713+00:00
-- url     : https://prove2.me/submissions/54cb4f4f-1e11-4b8b-8933-d537d27606b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralPieces_GenF_Exp
import Theorems.Thm_GeneralPieces_GenF_coeff_pow_eq_zero

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
omit [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution {a b : MvPowerSeries X R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {α : X →₀ ℕ} {i j : ℕ}
    (h : α.degree < i + j) : coeff α (a ^ i * b ^ j) = 0 := by
  classical
  rw [coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  have h' := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at h'
  by_cases h1 : p.1.degree < i
  · rw [coeff_pow_eq_zero ha h1, zero_mul]
  · rw [coeff_pow_eq_zero hb (by omega : p.2.degree < j), mul_zero]
end GeneralPieces.GenF
