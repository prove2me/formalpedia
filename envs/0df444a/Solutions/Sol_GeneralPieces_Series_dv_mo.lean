-- Prove2me | solution 1 for GeneralPieces.Series.dv_mo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:34:30.180291+00:00
-- url     : https://prove2.me/submissions/f697d4ed-7b2a-4312-a8d4-1d396f9f8598

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_cf_dv
import Theorems.Thm_GeneralPieces_Series_cf_mo
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_ext_cf
attribute [local simp] GeneralPieces.Series.cf_smul



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (a b : ℤ) : dv (mo a b) = (b : ℚ) • mo a (b - 1) := by
  refine ext_cf fun x y => ?_
  rw [cf_dv, cf_smul, cf_mo, cf_mo]
  by_cases h : x = a ∧ y = b - 1
  · rw [if_pos h, if_pos ⟨h.1, by omega⟩, h.2]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun g => h ⟨g.1, by omega⟩), mul_zero, mul_zero]
end GeneralPieces.Series
