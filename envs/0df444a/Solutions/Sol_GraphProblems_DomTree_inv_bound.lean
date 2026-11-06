-- Prove2me | solution 1 for GraphProblems.DomTree.inv_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:56.710283+00:00
-- url     : https://prove2.me/submissions/1f20415f-5f37-48c7-bc8a-94b1babb6e18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree

set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}
namespace GraphProblems.DomTree
theorem _root_.solution {n s w : ℕ} (x : DNode) (p t : ℕ) (h : Inv n s w x p t) : p ≤ 2 * n ∧ t ≤ n := by
  obtain ⟨-, a, V, h1, h2, h3, -⟩ := h
  omega
end GraphProblems.DomTree
