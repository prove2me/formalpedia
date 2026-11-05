-- Prove2me | solution 2 for GeneralPieces.Pcs.le_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:42.431143+00:00
-- url     : https://prove2.me/submissions/5db0387c-1c4f-40c9-ac7f-33d37c0c47c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_Le_smul
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_GeneralPieces_Pcs_le_tpow
import Theorems.Thm_GeneralPieces_Pcs_X_eq_tpow
import Theorems.Thm_GeneralPieces_Pcs_wt_singleton
import Theorems.Thm_GeneralPieces_LemQ_Tri_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (n : ℕ+) : Le n (y n) := by
  unfold y
  refine Le.sum _ fun j hj => Le.smul ?_ _
  rw [X_eq_tpow]
  refine le_tpow ?_
  rw [wt_singleton, PNat.toPNat'_coe (by have := (mem_Icc.1 hj).1; omega)]
  exact (mem_Icc.1 hj).2
end GeneralPieces.Pcs
