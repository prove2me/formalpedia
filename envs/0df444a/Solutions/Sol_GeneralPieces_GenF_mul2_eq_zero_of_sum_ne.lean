-- Prove2me | solution 1 for GeneralPieces.GenF.mul2_eq_zero_of_sum_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:05:47.879501+00:00
-- url     : https://prove2.me/submissions/8a68ea83-b601-448b-839d-b4e01d9e5be6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
import Theorems.Thm_ClauseBound_Boson_op_grade


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
namespace GeneralPieces.GenF
theorem _root_.solution (a b : List ℕ) {r r' : ℤ} (h : r + r' = 0) {π σ : Multiset ℕ} (hne : π.sum ≠ σ.sum) : mul2 a r b r' π σ = 0 := by
  unfold mul2
  refine Finset.sum_eq_zero fun τ _ => ?_
  by_contra h0
  have h1 := op_grade (left_ne_zero_of_mul h0)
  have h2 := op_grade (right_ne_zero_of_mul h0)
  exact hne (by omega)
end GeneralPieces.GenF
