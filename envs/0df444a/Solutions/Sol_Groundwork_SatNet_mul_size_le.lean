-- Prove2me | solution 1 for Groundwork.SatNet.mul_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:56:56.817979+00:00
-- url     : https://prove2.me/submissions/27a91373-679d-4cb2-9690-8a9cc6ff8149

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
theorem _root_.solution (m g k : ℕ) : g * (2 * k * ((m + g - 1) / g)) ≤ 2 * k * (m + g) := by
  have h : g * ((m + g - 1) / g) ≤ m + g := (Nat.mul_div_le _ _).trans (by omega)
  calc g * (2 * k * ((m + g - 1) / g)) = 2 * k * (g * ((m + g - 1) / g)) := by ring
    _ ≤ 2 * k * (m + g) := Nat.mul_le_mul_left _ h
end Groundwork.SatNet
