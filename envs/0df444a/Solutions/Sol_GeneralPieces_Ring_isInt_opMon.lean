-- Prove2me | solution 1 for GeneralPieces.Ring.isInt_opMon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:44:06.258792+00:00
-- url     : https://prove2.me/submissions/de44955e-b968-4e28-9c9a-e7e3f283d29f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_isInt_sum
import Theorems.Thm_GeneralPieces_Ring_isInt_term
import Theorems.Thm_GeneralPieces_Ring_exists_window
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_opWin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f : V} (hf : IsInt f) (μ : List ℕ+) (r : ℤ) : IsInt (opMon μ r f) := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE μ h1 h2]
  exact isInt_sum _ _ fun ks _ => isInt_term hf μ ks
end GeneralPieces.Ring
