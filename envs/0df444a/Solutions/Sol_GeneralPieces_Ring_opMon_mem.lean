-- Prove2me | solution 1 for GeneralPieces.Ring.opMon_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:41:14.13693+00:00
-- url     : https://prove2.me/submissions/46eb28c6-976e-4fb4-b65d-c174be5a586b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_term_mem
import Theorems.Thm_GeneralPieces_Ring_exists_window
import Theorems.Thm_GeneralPieces_Ring_opMon_eq_opWin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (r : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) : opMon μ r f ∈ VE (E + r) := by
  obtain ⟨E', M, hE, h1, h2⟩ := exists_window f r
  rw [opMon_eq_opWin hE μ h1 h2]
  refine Submodule.sum_mem _ fun ks hks => ?_
  have := term_mem μ ks hf
  rwa [(mem_filter.1 hks).2, sub_neg_eq_add] at this
end GeneralPieces.Ring
