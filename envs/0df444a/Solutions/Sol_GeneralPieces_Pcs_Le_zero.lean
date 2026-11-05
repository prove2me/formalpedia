-- Prove2me | solution 1 for GeneralPieces.Pcs.Le.zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:26.387962+00:00
-- url     : https://prove2.me/submissions/99f4c949-7174-40d5-a406-13563863df4d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_LemQ_coef_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
namespace Le
theorem _root_.solution (h : ℕ) : Le h 0 := fun π hπ => absurd (coef_zero π) hπ
end Le
end GeneralPieces.Pcs
