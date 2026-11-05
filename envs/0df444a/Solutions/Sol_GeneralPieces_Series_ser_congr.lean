-- Prove2me | solution 1 for GeneralPieces.Series.ser_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:38:19.174464+00:00
-- url     : https://prove2.me/submissions/ee17a468-14d8-43b6-8e3d-4975c9bcdb12

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (p q : ℕ) {c c' : ℤ → ℚ} (h : ∀ k, c k = c' k) : ser p q c = ser p q c' := by
  rw [funext h]
end GeneralPieces.Series
