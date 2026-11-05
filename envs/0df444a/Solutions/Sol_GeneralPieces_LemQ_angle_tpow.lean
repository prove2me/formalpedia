-- Prove2me | solution 1 for GeneralPieces.LemQ.angle_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:14:42.558196+00:00
-- url     : https://prove2.me/submissions/bcab0cde-15f2-4aec-8cc5-fd04c97e6292

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_part_tpow

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution {h : ℕ} (i : ℕ) {μ : Ptn} (hμ : wt μ ≤ h) : angle h i (tpow μ) = ((wt μ + h).choose i : ℚ) • tpow μ := by
  unfold angle
  simp only [part_tpow, smul_ite, smul_zero]
  rw [sum_ite_eq', if_pos (mem_range.2 (by omega))]
end GeneralPieces.LemQ
