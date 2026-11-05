-- Prove2me | solution 2 for GeneralPieces.Pcs.wt_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:16.708207+00:00
-- url     : https://prove2.me/submissions/dc6805cc-8c1d-42a5-a371-58e68e4a8a19

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (n : ℕ+) (μ : Ptn) : wt (n ::ₘ μ) = n + wt μ := by simp [wt]
end GeneralPieces.Pcs
