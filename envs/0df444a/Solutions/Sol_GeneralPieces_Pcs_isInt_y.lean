-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:28:20.386703+00:00
-- url     : https://prove2.me/submissions/1dcd376c-4cd6-47ec-8ae8-31123be783f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_X_eq_tpow
import Theorems.Thm_GeneralPieces_Pcs_isInt_sum
import Theorems.Thm_GeneralPieces_Pcs_isInt_smul
import Theorems.Thm_GeneralPieces_Pcs_isInt_tpow

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (n : ℕ+) : IsInt (y n) := by
  unfold y
  refine isInt_sum _ fun j _ => ?_
  have := isInt_smul (isInt_tpow {j.toPNat'}) ((n : ℕ).choose j : ℤ)
  rwa [Int.cast_natCast, ← X_eq_tpow] at this
end GeneralPieces.Pcs
