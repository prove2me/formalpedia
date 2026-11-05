-- Prove2me | solution 1 for GeneralPieces.Ring.finite_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:36:37.017285+00:00
-- url     : https://prove2.me/submissions/c3aa637a-fb00-4068-ac43-1bf252d79121

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_term_eq_zero_of_Bd
import Theorems.Thm_GeneralPieces_Ring_exists_window
import Theorems.Thm_ClauseBound_Boson_Text_mem_tup


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (r : ℤ) (f : V) : {ks ∈ Choices μ r | term μ ks f ≠ 0}.Finite := by
  obtain ⟨E, M, hE, h1, h2⟩ := exists_window f r
  refine (finite_toSet (ClauseBound.Boson.tup M μ.length)).subset fun ks hks => ?_
  obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hks
  refine mem_coe.2 (ClauseBound.Boson.Text.mem_tup.2 ⟨a1, fun k hk => ⟨a2 k hk, ?_⟩⟩)
  by_contra hcon
  exact a4 (term_eq_zero_of_Bd hE μ h1 h2 ks a3 ⟨k, hk, by omega⟩)
end GeneralPieces.Ring
