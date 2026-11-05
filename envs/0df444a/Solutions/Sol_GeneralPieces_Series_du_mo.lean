-- Prove2me | solution 1 for GeneralPieces.Series.du_mo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:34:18.765194+00:00
-- url     : https://prove2.me/submissions/ae656473-3fca-48c5-a9a3-e90b0ef53072

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_cf_du
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
theorem _root_.solution (a b : ℤ) : du (mo a b) = (a : ℚ) • mo (a - 1) b := by
  refine ext_cf fun x y => ?_
  rw [cf_du, cf_smul, cf_mo, cf_mo]
  by_cases h : x = a - 1 ∧ y = b
  · rw [if_pos h, if_pos ⟨by omega, h.2⟩, h.1]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun g => h ⟨by omega, g.2⟩), mul_zero, mul_zero]
end GeneralPieces.Series
