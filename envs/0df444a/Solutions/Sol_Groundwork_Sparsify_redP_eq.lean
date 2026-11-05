-- Prove2me | solution 1 for Groundwork.Sparsify.redP_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:25:21.476727+00:00
-- url     : https://prove2.me/submissions/d675abfa-4a2a-42b1-9fe7-f52fe277bf73

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
import Theorems.Thm_Groundwork_Sparsify_subP_iff

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
namespace Groundwork.Sparsify
theorem _root_.solution (s : PFml) : redP s = redLL s := by
  rw [redP, redLL]
  apply List.filter_congr
  intro C _
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  refine forall₂_congr fun D _ => ?_
  rw [← Bool.not_eq_true, subP_iff, subP_iff]
  tauto
end Groundwork.Sparsify
