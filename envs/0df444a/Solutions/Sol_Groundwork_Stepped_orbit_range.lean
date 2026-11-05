-- Prove2me | solution 1 for Groundwork.Stepped.orbit_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:38:43.483209+00:00
-- url     : https://prove2.me/submissions/d819e39f-c3df-4c56-a492-1f035945b54b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Finset
variable {α β γ : Type}
namespace Groundwork.Stepped
theorem _root_.solution (N : α → ℕ) (a : α) (k y : ℕ) (h : y + k = N a) :
    Orbit (rangeNext N) (if y < N a then some (a, y) else none) ((List.range' y k).map fun y => (a, y)) := by
  induction k generalizing y with
  | zero => rw [if_neg (by omega)]; exact .nil
  | succ k ih =>
    rw [if_pos (by omega), List.range'_succ, List.map_cons]
    exact .cons (ih (y + 1) (by omega))
end Groundwork.Stepped
