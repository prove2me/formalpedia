-- Prove2me | solution 1 for GraphProblems.DomTree.sat_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:35.61354+00:00
-- url     : https://prove2.me/submissions/a120806e-9c7e-4781-9ae8-c4b85e66521c

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
theorem _root_.solution {C : List (ℕ × Bool)} {ψ : Fml} : Sat a (C :: ψ) ↔ (∃ l ∈ C, ext a l.1 = l.2) ∧ Sat a ψ := List.forall_mem_cons
end GraphProblems.DomTree
