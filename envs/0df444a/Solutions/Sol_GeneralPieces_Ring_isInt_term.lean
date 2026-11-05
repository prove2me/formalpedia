-- Prove2me | solution 1 for GeneralPieces.Ring.isInt_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:42:49.125453+00:00
-- url     : https://prove2.me/submissions/00ef0782-917f-42d6-baca-3ce741124c7e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_isInt_zsmul
import Theorems.Thm_GeneralPieces_Ring_isInt_foldr
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f : V} (hf : IsInt f) (μ : List ℕ+) (ks : List ℤ) : IsInt (term μ ks f) := by
  rw [term_eq]
  exact isInt_zsmul (isInt_foldr (isInt_foldr hf _) _) _
end GeneralPieces.Ring
