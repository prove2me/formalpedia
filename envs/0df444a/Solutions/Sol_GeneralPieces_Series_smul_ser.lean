-- Prove2me | solution 1 for GeneralPieces.Series.smul_ser
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:24:10.146716+00:00
-- url     : https://prove2.me/submissions/48c2f323-fea1-4812-bb25-d82a41d329e4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_cf_ser
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_ext_cf
attribute [local simp] GeneralPieces.Series.cf_smul



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (r : ℚ) (p q : ℕ) (c : ℤ → ℚ) : r • ser p q c = ser p q fun k => r * c k := by
  refine ext_cf fun x y => ?_
  rw [cf_smul, cf_ser, cf_ser]
  split_ifs
  · rfl
  · rw [mul_zero]
end GeneralPieces.Series
