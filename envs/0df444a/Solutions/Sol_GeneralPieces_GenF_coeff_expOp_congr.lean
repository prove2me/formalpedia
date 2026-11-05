-- Prove2me | solution 1 for GeneralPieces.GenF.coeff_expOp_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:43:08.857877+00:00
-- url     : https://prove2.me/submissions/80fba881-4b8b-48bf-bf80-dec0407fa28a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Exp
import Mathlib.Algebra.MvPolynomial.Derivation
import Definitions.Def_GeneralPieces_GenF_Taylor
import Theorems.Thm_GeneralPieces_GenF_coeff_rat_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (O : X → A →ₗ[ℚ] A) (α : X →₀ ℕ) (f g : MvPowerSeries X A) (h : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β g) :
    coeff α (expOp O f) = coeff α (expOp O g) := by
  have hl : Low (α.degree + 1) (f - g) := fun β hβ => by rw [map_sub, h β (by omega), sub_self]
  have h0 : coeff α (expOp O (f - g)) = 0 := by
    rw [coeff_expOp_def]
    unfold opN
    rw [map_sum]
    exact sum_eq_zero fun n _ => by rw [coeff_rat_smul, hl.iterate O n α (by omega), smul_zero]
  have h1 : f = (f - g) + g := (sub_add_cancel f g).symm
  rw [h1, expOp_add, map_add, h0, zero_add]
end GeneralPieces.GenF
