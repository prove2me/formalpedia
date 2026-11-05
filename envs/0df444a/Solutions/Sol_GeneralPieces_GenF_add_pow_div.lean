-- Prove2me | solution 1 for GeneralPieces.GenF.add_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:37:36.966472+00:00
-- url     : https://prove2.me/submissions/219172e0-0f25-422e-b4bb-484d16e4ee55

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

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (a b : MvPowerSeries X R) (n : ℕ) :
    ((n.factorial : ℚ)⁻¹) • (a + b) ^ n = ∑ p ∈ antidiagonal n, ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • (a ^ p.1 * b ^ p.2) := by
  rw [(Commute.all a b).add_pow', smul_sum]
  refine sum_congr rfl fun p hp => ?_
  have hn := mem_antidiagonal.1 hp
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
  rw [hn, ← Nat.choose_symm_of_eq_add hn.symm] at h
  have h' : ((n.choose p.1 : ℕ) : ℚ) * p.1.factorial * p.2.factorial = n.factorial := by exact_mod_cast h
  have h1 : (p.1.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (p.2.factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith
end GeneralPieces.GenF
