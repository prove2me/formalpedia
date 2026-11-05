-- Prove2me | solution 2 for GeneralPieces.Pcs.one_le_pZ
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:27:33.656418+00:00
-- url     : https://prove2.me/submissions/d508f5e8-eafb-48af-97bb-1f28d68cb36a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_one_le_p
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem solution {m : ℤ} (hm : 0 ≤ m) : 1 ≤ pZ m := by
  rw [pZ, if_pos hm]
  exact GeneralPieces.Pcs.one_le_p _
