-- Prove2me | solution 1 for GeneralPieces.Ring.mem_ptns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:31:20.117825+00:00
-- url     : https://prove2.me/submissions/7bca483a-1fa8-4f0d-b2c1-b964cd535d18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133
import Theorems.Thm_P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b
import Theorems.Thm_GeneralPieces_Ring_sum_toN
import Theorems.Thm_GeneralPieces_Ring_zero_notMem_toN


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (E : ℕ) (μ : Ptn) : μ ∈ ptns E ↔ wt μ = E := by
  unfold ptns
  rw [mem_image]
  constructor
  · rintro ⟨q, -, rfl⟩
    rw [← sum_toN, toN_map_toPNat' fun i hi => q.parts_pos hi, q.parts_sum]
  · intro h
    refine ⟨⟨toN μ, fun {i} hi => Nat.pos_of_ne_zero fun h0 => zero_notMem_toN μ (h0 ▸ hi), h⟩, mem_univ _, map_toPNat'_toN μ⟩
end GeneralPieces.Ring
