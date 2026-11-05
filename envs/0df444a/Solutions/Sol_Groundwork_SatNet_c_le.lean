-- Prove2me | solution 1 for Groundwork.SatNet.c_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:40:36.264442+00:00
-- url     : https://prove2.me/submissions/3aed50c7-1ab7-4f2d-a5b5-be03a3acc28f

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
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (a b : Fin g) :
    (net φ g μ k).c a b ≤ #{s : Sl μ k | Out φ a b s} + #{s : Sl μ k | Out φ b a s} := by
  simp only [net]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]; omega
  · rw [min_eq_right h, max_eq_left h]; omega
end Groundwork.SatNet
