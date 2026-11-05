-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_opN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:48:54.682439+00:00
-- url     : https://prove2.me/submissions/ef47bb10-94fe-4273-b0a3-d61517e3c606

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Theorems.Thm_GeneralPieces_GenF_inv_factorial_succ_mul
import Theorems.Thm_GeneralPieces_GenF_pderiv_iterate

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (N : ℕ) (f : MvPowerSeries X A) :
    pderiv A i (opN O (N + 1) f) = opN O (N + 1) (pderiv A i f) + opN O N (mapE (O i) f) := by
  unfold opN
  rw [sum_range_succ', sum_range_succ' (fun n => ((n.factorial : ℚ)⁻¹) • (opX O)^[n] (pderiv A i f)), map_add, map_sum, add_right_comm, ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun n _ => ?_
    rw [map_rat_smul, pderiv_iterate hc, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_factorial_succ_mul]
  · rw [map_rat_smul]
    rfl
end GeneralPieces.GenF
