-- Prove2me | solution 1 for GeneralPieces.Dual.eq_of_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:21:00.752736+00:00
-- url     : https://prove2.me/submissions/2d948f7d-a10a-4881-bfe5-a120cd22f595

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ ν : Ptn) (hc : ∀ k, μ.count k ≤ ν.count k) (hw : wt μ = wt ν) : μ = ν := by
  obtain ⟨ρ, rfl⟩ := Multiset.le_iff_exists_add.1 (Multiset.le_iff_count.2 hc)
  rcases Multiset.empty_or_exists_mem ρ with rfl | ⟨a, ha⟩
  · simp
  · obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    have := a.pos
    simp only [wt, Multiset.map_add, Multiset.sum_add, Multiset.map_cons, Multiset.sum_cons] at hw
    omega
end GeneralPieces.Dual
