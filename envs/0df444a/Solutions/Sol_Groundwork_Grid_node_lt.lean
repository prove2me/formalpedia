-- Prove2me | solution 1 for Groundwork.Grid.node_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:38:13.931412+00:00
-- url     : https://prove2.me/submissions/484bbb54-2d7e-4df7-9c58-150b0ab2e44a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution {g : ℕ} (tr : Bool) {a i : ℕ} (ha : a < g) (hi : i < g) : node g tr a i < g * g := by
  have key : ∀ {a i : ℕ}, a < g → i < g → i + g * a < g * g := fun {a i} ha hi =>
    calc i + g * a < g + g * a := by omega
      _ = g * (a + 1) := by ring
      _ ≤ g * g := Nat.mul_le_mul_left _ ha
  cases tr
  · exact key ha hi
  · exact key hi ha
end Groundwork.Grid
