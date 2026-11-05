-- Prove2me | solution 1 for GraphProblems.DomTree.sat_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:22:36.707196+00:00
-- url     : https://prove2.me/submissions/5ac56d0c-ed9a-42de-ad37-2e45f5afaa67

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
theorem _root_.solution {ψ φ : Fml} : Sat a (ψ ++ φ) ↔ Sat a ψ ∧ Sat a φ := List.forall_mem_append
end GraphProblems.DomTree
