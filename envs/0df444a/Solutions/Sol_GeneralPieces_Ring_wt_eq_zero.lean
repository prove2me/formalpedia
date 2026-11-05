-- Prove2me | solution 1 for GeneralPieces.Ring.wt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:22:43.237331+00:00
-- url     : https://prove2.me/submissions/34ab58c7-c524-4cf0-b940-26635975814c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_mem_toN
import Theorems.Thm_GeneralPieces_Ring_sum_toN


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {μ : Ptn} (h : wt μ = 0) : μ = 0 := by
  rw [← sum_toN, Multiset.sum_eq_zero_iff] at h
  refine Multiset.eq_zero_of_forall_notMem fun k hk => ?_
  exact k.pos.ne' (h _ ((mem_toN μ k).2 hk))
end GeneralPieces.Ring
