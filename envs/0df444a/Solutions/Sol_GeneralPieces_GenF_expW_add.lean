-- Prove2me | solution 1 for GeneralPieces.GenF.expW_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:50:28.665146+00:00
-- url     : https://prove2.me/submissions/cf2cf47a-78eb-477c-ad84-444b80aa4642

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
import Theorems.Thm_GeneralPieces_GenF_sum_triangle
import Theorems.Thm_GeneralPieces_GenF_coeff_expW_def
import Theorems.Thm_GeneralPieces_GenF_coeff_rat_smul
import Theorems.Thm_GeneralPieces_GenF_coeff_expW
import Theorems.Thm_GeneralPieces_GenF_coeff_mul_congr
import Theorems.Thm_GeneralPieces_GenF_coeff_pow_mul_pow_eq_zero
import Theorems.Thm_GeneralPieces_GenF_add_pow_div

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution {a b : MvPowerSeries X R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) : expW (a + b) = expW a * expW b := by
  ext α
  have hab : constantCoeff (a + b) = 0 := by rw [map_add, ha, hb, add_zero]
  rw [coeff_mul_congr (f' := expN (α.degree + 1) a) (g' := expN (α.degree + 1) b) (fun β hβ => coeff_expW ha (by omega)) fun β hβ => coeff_expW hb (by omega),
    coeff_expW_def]
  unfold expN
  rw [sum_mul_sum, map_sum, map_sum]
  simp only [add_pow_div, map_sum, smul_mul_smul_comm]
  refine sum_triangle (α.degree + 1) (fun i j => coeff α (((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹) • (a ^ i * b ^ j))) fun i j hij => ?_
  rw [coeff_rat_smul, coeff_pow_mul_pow_eq_zero ha hb (by omega), smul_zero]
end GeneralPieces.GenF
