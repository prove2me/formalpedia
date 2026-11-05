-- Prove2me | solution 1 for GeneralPieces.Ring.opMon_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:58.357202+00:00
-- url     : https://prove2.me/submissions/231724b4-b4ec-4d63-944a-026878cdd49d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_exists_Bd
import Theorems.Thm_GeneralPieces_Ring_Bd_mono
import Theorems.Thm_GeneralPieces_Ring_Bd_add
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_opWin
import Theorems.Thm_GeneralPieces_Ring_opWin_add

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (r : ℤ) (f g : V) : opMon μ r (f + g) = opMon μ r f + opMon μ r g := by
  obtain ⟨E, hE⟩ := exists_Bd f
  obtain ⟨E', hE'⟩ := exists_Bd g
  have hf : Bd f ((E + E' : ℕ) : ℤ) := hE.mono (by push_cast; omega)
  have hg : Bd g ((E + E' : ℕ) : ℤ) := hE'.mono (by push_cast; omega)
  have h1 : ((E + E' : ℕ) : ℤ) ≤ ((E + E' + r.natAbs : ℕ) : ℤ) := by omega
  have h2 : ((E + E' : ℕ) : ℤ) + r ≤ ((E + E' + r.natAbs : ℕ) : ℤ) := by omega
  rw [opMon_eq_opWin (hf.add hg) μ h1 h2, opMon_eq_opWin hf μ h1 h2, opMon_eq_opWin hg μ h1 h2, opWin_add]
end GeneralPieces.Ring
