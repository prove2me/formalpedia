-- Prove2me | solution 1 for Groundwork.Colouring.beta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:06.992128+00:00
-- url     : https://prove2.me/submissions/daa4d2a6-0866-43b0-9487-a0500af2e07a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semifield
import Definitions.Def_Groundwork_Net_Colouring

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
namespace Groundwork.Colouring
theorem _root_.solution (K g U P : ℕ) : K ^ 3 * beta K g U P ≤ K ^ 3 + K * U + g * P := by
  unfold beta
  have := Nat.mul_div_le (K * U + g * P) (K ^ 3)
  rcases le_total 1 ((K * U + g * P) / K ^ 3) with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega
end Groundwork.Colouring
