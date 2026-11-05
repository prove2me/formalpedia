-- Prove2me | solution 1 for GeneralPieces.Ring.coef_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:38.469344+00:00
-- url     : https://prove2.me/submissions/1cc8e0b2-1c8c-433b-8d92-2fd2aa951ab1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (π : Ptn) (q : ℚ) (f : V) : coef π (q • f) = q * coef π f := by
  unfold coef
  rw [coeff_smul, smul_eq_mul]
end GeneralPieces.Ring
