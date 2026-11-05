-- Prove2me | solution 1 for GeneralPieces.Dual.mem_posTuples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:17:19.491219+00:00
-- url     : https://prove2.me/submissions/1adf7a27-314c-4997-abaf-84be4e402318

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_mem_tuples
import Theorems.Thm_P2M_GeneralPieces_Dual_forall__replicate_53e3e372b2d2

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (r h : ℕ) (ks : List ℤ) : ks ∈ posTuples r h ↔ ks.length = r ∧ (∀ k ∈ ks, 1 ≤ k) ∧ ks.sum = h := by
  rw [posTuples, mem_filter, mem_tuples, forall₂_replicate]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun k hk => (mem_Icc.1 (h2 k hk)).1, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun k hk => mem_Icc.2 ⟨h2 k hk, ?_⟩⟩, h3⟩
    rw [← h3]
    exact List.single_le_sum (fun x hx => by have := h2 x hx; omega) k hk
end GeneralPieces.Dual
