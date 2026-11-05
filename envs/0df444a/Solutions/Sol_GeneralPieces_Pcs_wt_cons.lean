-- Prove2me | solution 1 for GeneralPieces.Pcs.wt_cons
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:08:26.234911+00:00
-- url     : https://prove2.me/submissions/2a77f340-41c7-4716-bbe2-9ba113fcf1a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_ClauseBound_Boson_Text_wt_cons

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem solution (n : ℕ+) (μ : Ptn) : wt (n ::ₘ μ) = n + wt μ := by
  simp [wt]
