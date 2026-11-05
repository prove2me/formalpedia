-- Prove2me | solution 1 for Groundwork.Sparsify.mem_litsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:25:59.520755+00:00
-- url     : https://prove2.me/submissions/76b7e3a1-7094-4934-aa30-45148a113877

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

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
namespace Groundwork.Sparsify
theorem _root_.solution {s : PFml} {C : PCl} (hC : C ∈ s) {a : PLit} (ha : a ∈ C) : a ∈ litsOf s := by
  simp only [litsOf, List.mem_dedup, List.mem_flatMap, id]
  exact ⟨C, hC, ha⟩
end Groundwork.Sparsify
