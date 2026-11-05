-- Prove2me | solution 1 for Groundwork.Sparsify.toFinset_redL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:24:47.763618+00:00
-- url     : https://prove2.me/submissions/f27ceb24-f43f-4c0d-9157-a77471318b48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_SparsifyTree
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_StepMachines_Math_SparsifyStep

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
namespace Groundwork.Sparsify
theorem _root_.solution (s : List (Finset α)) : (redL s).toFinset = red s.toFinset := by
  ext C
  simp [redL, red]
end Groundwork.Sparsify
