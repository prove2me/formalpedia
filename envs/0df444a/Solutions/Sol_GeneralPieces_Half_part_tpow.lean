-- Prove2me | solution 1 for GeneralPieces.Half.part_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:43:31.035446+00:00
-- url     : https://prove2.me/submissions/55499a5c-50cb-4fc3-b254-8d2409a28ff4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Ring_VE_natCast
import Theorems.Thm_GeneralPieces_Ring_tpow_mem_VE


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution (h' : ℕ) (μ : Ptn) : part h' (tpow μ) = if h' = wt μ then tpow μ else 0 := by
  have h : tpow μ ∈ weightedHomogeneousSubmodule ℚ wgt (wt μ) := by
    have := tpow_mem_VE μ
    rwa [VE_natCast] at this
  exact weightedHomogeneousComponent_of_mem h
end GeneralPieces.Half
