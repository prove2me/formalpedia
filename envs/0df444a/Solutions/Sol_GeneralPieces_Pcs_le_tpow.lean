-- Prove2me | solution 1 for GeneralPieces.Pcs.le_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:58.532219+00:00
-- url     : https://prove2.me/submissions/9f6439ca-256f-4c30-b1ef-4a8449f2c18c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Ring_coef_tpow


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution {h : ℕ} {μ : Ptn} (hμ : wt μ ≤ h) : Le h (tpow μ) := fun π hπ => by
  rw [coef_tpow] at hπ
  by_cases e : π = μ
  · rw [e]; exact hμ
  · rw [if_neg e] at hπ; exact absurd rfl hπ
end GeneralPieces.Pcs
