-- Prove2me | solution 1 for GeneralPieces.Ring.mem_ptnsZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:46.751722+00:00
-- url     : https://prove2.me/submissions/2abc9b9d-2b61-435f-baf1-16231e8c7cd0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_mem_ptns

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (E : ℤ) (μ : Ptn) : μ ∈ ptnsZ E ↔ (wt μ : ℤ) = E := by
  unfold ptnsZ
  split_ifs with h
  · rw [mem_ptns]; omega
  · simp only [notMem_empty, false_iff]; omega
end GeneralPieces.Ring
