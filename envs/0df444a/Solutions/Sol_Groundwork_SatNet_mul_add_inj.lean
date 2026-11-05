-- Prove2me | solution 1 for Groundwork.SatNet.mul_add_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:30.529104+00:00
-- url     : https://prove2.me/submissions/d4c6ebc8-71e9-4be4-94d9-cc4c848d98fd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
namespace Groundwork.SatNet
theorem _root_.solution {k x y j j' : ℕ} (hj : j < k) (hj' : j' < k) (h : x * k + j = y * k + j') :
    x = y ∧ j = j' := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this; omega
  · subst heq; exact ⟨rfl, by omega⟩
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at this; omega
end Groundwork.SatNet
