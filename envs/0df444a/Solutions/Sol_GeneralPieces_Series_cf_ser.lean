-- Prove2me | solution 1 for GeneralPieces.Series.cf_ser
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:37:56.814872+00:00
-- url     : https://prove2.me/submissions/2461410e-379d-455a-bf7c-4dd73bd378e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_cf_diag


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (p q : ℕ) (c : ℤ → ℚ) (x y : ℤ) : cf (ser p q c) x y = if 1 ≤ y + q ∧ x + y = -((p : ℤ) + q) then c (y + q) else 0 := by
  rw [ser, cf_diag]
  exact if_congr (by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩) rfl rfl
end GeneralPieces.Series
