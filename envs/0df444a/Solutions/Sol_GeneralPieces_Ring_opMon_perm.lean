-- Prove2me | solution 1 for GeneralPieces.Ring.opMon_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:41:36.896338+00:00
-- url     : https://prove2.me/submissions/83a29409-068c-494c-b869-0a1af04cc103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_opWin
import Theorems.Thm_GeneralPieces_Ring_exists_window
import Theorems.Thm_GeneralPieces_Ring_opWin_perm

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {μ μ' : List ℕ+} (h : μ.Perm μ') (r : ℤ) (f : V) : opMon μ r f = opMon μ' r f := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE μ h1 h2, opMon_eq_opWin hE μ' h1 h2, opWin_perm h]
end GeneralPieces.Ring
