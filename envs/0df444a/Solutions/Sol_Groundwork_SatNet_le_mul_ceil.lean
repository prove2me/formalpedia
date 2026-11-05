-- Prove2me | solution 1 for Groundwork.SatNet.le_mul_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:09.977147+00:00
-- url     : https://prove2.me/submissions/64251e3f-1b70-4335-a030-c9cfdc07554f

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
namespace Groundwork.SatNet
theorem _root_.solution (m : ℕ) {g : ℕ} (hg : 0 < g) : m ≤ g * ((m + g - 1) / g) := by
  have := Nat.div_add_mod (m + g - 1) g
  have := Nat.mod_lt (m + g - 1) hg
  omega
end Groundwork.SatNet
