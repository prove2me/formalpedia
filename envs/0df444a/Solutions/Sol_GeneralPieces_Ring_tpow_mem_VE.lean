-- Prove2me | solution 1 for GeneralPieces.Ring.tpow_mem_VE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:08.406312+00:00
-- url     : https://prove2.me/submissions/817cf9cb-e186-4b46-90ee-e3be3b5cb693

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp
import Theorems.Thm_GeneralPieces_Ring_mem_VE_natCast

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : Ptn) : tpow μ ∈ VE (wt μ : ℤ) := by
  rw [mem_VE_natCast]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_toFinsupp μ)
end GeneralPieces.Ring
