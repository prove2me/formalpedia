-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_expN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:27.598989+00:00
-- url     : https://prove2.me/submissions/47380c8c-5984-46d0-a1a0-e2f791e3554a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Theorems.Thm_GeneralPieces_GenF_inv_factorial_succ_mul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (i : X) (N : ℕ) (w : MvPowerSeries X A) : pderiv A i (expN (N + 1) w) = pderiv A i w * expN N w := by
  unfold expN
  rw [sum_range_succ', map_add, map_sum, mul_sum]
  have h0 : pderiv A i (((Nat.factorial 0 : ℚ)⁻¹) • w ^ 0) = 0 := by rw [map_rat_smul, pow_zero, pderiv_one, smul_zero]
  rw [h0, add_zero]
  refine sum_congr rfl fun n _ => ?_
  rw [map_rat_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_factorial_succ_mul,
    mul_smul_comm, mul_comm]
end GeneralPieces.GenF
