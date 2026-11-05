-- Prove2me | solution 1 for GeneralPieces.Ring.opMon_eq_opWin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:21:13.066836+00:00
-- url     : https://prove2.me/submissions/e1fbff70-009e-4c2d-9dc8-85380d3326c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_term_eq_zero_of_Bd
import Theorems.Thm_ClauseBound_Boson_Text_mem_tup


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f : V} {E : ℤ} (hf : Bd f E) (μ : List ℕ+) {r : ℤ} {M : ℕ} (h1 : E ≤ M) (h2 : E + r ≤ M) : opMon μ r f = opWin μ M r f := by
  unfold opMon opWin
  refine finsum_mem_eq_sum_of_subset _ (fun ks hks => ?_) fun ks hks => ?_
  · obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hks
    refine mem_coe.2 (mem_filter.2 ⟨ClauseBound.Boson.Text.mem_tup.2 ⟨a1, fun k hk => ⟨a2 k hk, ?_⟩⟩, a3⟩)
    by_contra hcon
    exact a4 (term_eq_zero_of_Bd hf μ h1 h2 ks a3 ⟨k, hk, by omega⟩)
  · obtain ⟨a1, a2⟩ := mem_filter.1 (mem_coe.1 hks)
    obtain ⟨a3, a4⟩ := ClauseBound.Boson.Text.mem_tup.1 a1
    exact ⟨a3, fun k hk => (a4 k hk).1, a2⟩
end GeneralPieces.Ring
