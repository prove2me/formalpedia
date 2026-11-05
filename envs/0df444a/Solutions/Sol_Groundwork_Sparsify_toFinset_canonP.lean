-- Prove2me | solution 1 for Groundwork.Sparsify.toFinset_canonP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:29:37.507993+00:00
-- url     : https://prove2.me/submissions/5d40bdd5-7d2e-441c-882f-355ad15910d8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyList
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Definitions.Def_StepMachines_Math_SparsifyProg
import Theorems.Thm_Groundwork_Sparsify_mem_litsOf

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {τ n : ℕ} {ψ s l h : PFml} {p q : ℕ}
namespace Groundwork.Sparsify
theorem _root_.solution {C : PCl} (hC : C ∈ ψ) : (canonP (litsOf ψ) C).toFinset = C.toFinset := by
  ext a
  simp only [canonP, List.mem_toFinset, List.mem_filter, List.elem_eq_mem, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_litsOf hC h, h⟩⟩
end Groundwork.Sparsify
