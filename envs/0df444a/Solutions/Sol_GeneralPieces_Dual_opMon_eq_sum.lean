-- Prove2me | solution 1 for GeneralPieces.Dual.opMon_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:18:22.684434+00:00
-- url     : https://prove2.me/submissions/aee71a04-65dd-45d3-87af-73f985768125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_mem_posTuples
import Theorems.Thm_GeneralPieces_o3


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (h : ℕ) (μ : List ℕ+) (b : V) (hb : b ∈ VE h) :
    opMon μ (-(h : ℤ)) b = ∑ ks ∈ posTuples μ.length h, term μ ks b := by
  unfold opMon
  apply finsum_mem_eq_sum_of_inter_support_eq
  ext ks
  simp only [Set.mem_inter_iff, Function.mem_support, mem_coe, mem_posTuples, Choices, Set.mem_ofPred_eq, neg_neg]
  constructor
  · rintro ⟨⟨hl, hne, hs⟩, ht⟩
    refine ⟨⟨hl, fun k hk => ?_, hs⟩, ht⟩
    by_contra hc
    have hk0 := hne k hk
    exact ht (o3.positive h μ b ks hb ⟨hl, hne, by rw [hs, neg_neg]⟩ ⟨k, hk, by omega⟩)
  · rintro ⟨⟨hl, hpos, hs⟩, ht⟩
    exact ⟨⟨hl, fun k hk => by have := hpos k hk; omega, hs⟩, ht⟩
end GeneralPieces.Dual
