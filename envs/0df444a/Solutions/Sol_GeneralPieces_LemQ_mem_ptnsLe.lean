-- Prove2me | solution 1 for GeneralPieces.LemQ.mem_ptnsLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:56.654886+00:00
-- url     : https://prove2.me/submissions/b245c3f7-1fbc-40fa-9841-087d6a30c0f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_Ring_mem_ptns


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (h : ℕ) (μ : Ptn) : μ ∈ ptnsLe h ↔ wt μ ≤ h := by
  unfold ptnsLe
  simp only [mem_biUnion, mem_range, mem_ptns]
  exact ⟨fun ⟨e, h1, h2⟩ => by omega, fun h1 => ⟨_, by omega, rfl⟩⟩
end GeneralPieces.LemQ
