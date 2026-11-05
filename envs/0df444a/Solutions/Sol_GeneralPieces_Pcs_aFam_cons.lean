-- Prove2me | solution 1 for GeneralPieces.Pcs.aFam_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:44.711546+00:00
-- url     : https://prove2.me/submissions/9a55e4d0-729b-423d-8edb-c1c8e4d32332

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
theorem _root_.solution (n : ℕ+) (μ : Ptn) : aFam (n ::ₘ μ) = ((-1 : ℚ) ^ ((n : ℕ) - 1) • y n) * aFam μ := by
  unfold aFam
  rw [Multiset.map_cons, Multiset.prod_cons]
end GeneralPieces.Pcs
