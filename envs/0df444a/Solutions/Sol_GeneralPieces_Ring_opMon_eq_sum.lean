-- Prove2me | solution 1 for GeneralPieces.Ring.opMon_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:29:47.158943+00:00
-- url     : https://prove2.me/submissions/2f1331ac-22ed-45f4-899a-9a02d1a89345

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_term_eq_zero
import Theorems.Thm_ClauseBound_Boson_Text_mem_tup


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (r : ℤ) (σ : Ptn) (M : ℕ) (hM : (wt σ : ℤ) + |r| ≤ M) :
    opMon μ r (tpow σ) = ∑ ks ∈ ClauseBound.Boson.tup M μ.length with ks.sum = -r, term μ ks (tpow σ) := by
  unfold opMon
  refine finsum_mem_eq_sum_of_subset _ (fun ks hks => ?_) fun ks hks => ?_
  · obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hks
    refine mem_coe.2 (mem_filter.2 ⟨ClauseBound.Boson.Text.mem_tup.2 ⟨h1, fun k hk => ⟨h2 k hk, ?_⟩⟩, h3⟩)
    by_contra hcon
    exact h4 (term_eq_zero μ r σ ks h3 ⟨k, hk, by omega⟩)
  · obtain ⟨h1, h2⟩ := mem_filter.1 (mem_coe.1 hks)
    obtain ⟨h3, h4⟩ := ClauseBound.Boson.Text.mem_tup.1 h1
    exact ⟨h3, fun k hk => (h4 k hk).1, h2⟩
end GeneralPieces.Ring
