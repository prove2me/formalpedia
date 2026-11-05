-- Prove2me | solution 1 for GeneralPieces.Ring.wt_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:35:53.098041+00:00
-- url     : https://prove2.me/submissions/0753eb6b-04d8-4cdb-96a3-63058c4ce088

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_toN_erase
import Theorems.Thm_GeneralPieces_Ring_mem_toN
import Theorems.Thm_GeneralPieces_Ring_sum_toN

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {σ : Ptn} {l : ℕ+} (h : l ∈ σ) : wt (σ.erase l) + l = wt σ := by
  rw [← sum_toN, ← sum_toN, toN_erase, add_comm]
  exact Multiset.sum_erase ((mem_toN σ l).2 h)
end GeneralPieces.Ring
