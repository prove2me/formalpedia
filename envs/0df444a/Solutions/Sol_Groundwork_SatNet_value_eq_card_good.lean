-- Prove2me | solution 1 for Groundwork.SatNet.value_eq_card_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:02.387614+00:00
-- url     : https://prove2.me/submissions/168a4ca0-1b25-4475-b685-d91f48b9fb37

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
import Theorems.Thm_Groundwork_SatNet_term_eq

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution : (net φ g μ k).value = #{z | Good φ (g := g) (μ := μ) (k := k) z} := by
  unfold Network.value
  rw [Finset.sum_congr rfl fun z _ => term_eq z]
  simp [net]
end Groundwork.SatNet
