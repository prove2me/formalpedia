-- Prove2me | solution 1 for Groundwork.Sparsify.map_redLL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:24:50.055435+00:00
-- url     : https://prove2.me/submissions/3b2816d8-86aa-415a-816a-ef0938358e41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyStep
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_ThreeSatStatement
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_StepMachines_Math_SparsifyList

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
namespace Groundwork.Sparsify
theorem _root_.solution (s : List (List α)) : (redLL s).map List.toFinset = redL (s.map List.toFinset) := by
  rw [redLL, redL, List.filter_map]
  congr 1
  apply List.filter_congr
  intro C _
  simp only [Function.comp, List.forall_mem_map, decide_eq_decide]
  refine forall₂_congr fun D _ => ?_
  constructor
  · intro h hDC
    exact Finset.Subset.antisymm hDC fun a ha =>
      List.mem_toFinset.2 (h (fun a ha => List.mem_toFinset.1 (hDC (List.mem_toFinset.2 ha))) a (List.mem_toFinset.1 ha))
  · intro h hDC a ha
    have := h fun a ha => List.mem_toFinset.2 (hDC a (List.mem_toFinset.1 ha))
    exact List.mem_toFinset.1 (this ▸ List.mem_toFinset.2 ha)
end Groundwork.Sparsify
