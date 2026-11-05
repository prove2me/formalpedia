-- Prove2me | solution 1 for GeneralPieces.Series.deriv_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:24:02.303178+00:00
-- url     : https://prove2.me/submissions/3bdc4318-4cb1-4730-9c17-f332939e3cb1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
variable {A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.Series
theorem _root_.solution (D : Derivation ℚ A A) {ε : A} {s : ℚ} (h : D ε = s • ε ^ 2) (m : ℕ) : D (ε ^ m) = (s * m) • ε ^ (m + 1) := by
  rcases m with _ | m
  · simp
  · rw [D.leibniz_pow, h, Nat.add_sub_cancel, smul_eq_mul, mul_smul_comm, ← pow_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_comm s]
end GeneralPieces.Series
