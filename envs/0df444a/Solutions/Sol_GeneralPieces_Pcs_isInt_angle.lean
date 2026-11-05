-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_angle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:28:21.786062+00:00
-- url     : https://prove2.me/submissions/c26206b0-efce-43ae-9c1e-a46f60ba9972

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_isInt_sum
import Theorems.Thm_GeneralPieces_Pcs_isInt_smul
import Theorems.Thm_GeneralPieces_Pcs_isInt_part

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution {a : V} (ha : IsInt a) (h i : ℕ) : IsInt (angle h i a) := by
  unfold angle
  refine isInt_sum _ fun h' _ => ?_
  have := isInt_smul (isInt_part ha h') ((h' + h).choose i : ℤ)
  rwa [Int.cast_natCast] at this
end GeneralPieces.Pcs
