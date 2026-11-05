-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:29.219347+00:00
-- url     : https://prove2.me/submissions/7ee486e6-eea0-484c-b743-ea3943c75167

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Mathlib.Data.Finsupp.Multiset
import Definitions.Def_GeneralPieces_GenF_Coeff
import Theorems.Thm_GeneralPieces_GenF_coeff_lin
import Theorems.Thm_GeneralPieces_GenF_degree_add_single


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
omit [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution (c : X → A) (i : X) : pderiv A i (lin c) = C (c i) := by
  classical
  ext α
  rw [coeff_pderiv, coeff_lin, degree_add_single, coeff_C]
  by_cases h : α = 0
  · subst h
    rw [map_zero, zero_add, if_pos rfl, zero_add, Finsupp.support_single i one_ne_zero, sum_singleton, if_pos rfl]
    simp
  · have h' : α.degree ≠ 0 := fun h0 => h ((Finsupp.degree_eq_zero_iff α).1 h0)
    rw [if_neg (by omega), if_neg h, zero_mul]
end GeneralPieces.GenF
