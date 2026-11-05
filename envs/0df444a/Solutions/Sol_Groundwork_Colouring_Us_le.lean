-- Prove2me | solution 1 for Groundwork.Colouring.Us_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:53.217339+00:00
-- url     : https://prove2.me/submissions/ee3054f0-2a86-4719-97f2-7b911976633a

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
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
variable (c : ι → ι → ℕ)
omit [DecidableEq ι]
namespace Groundwork.Colouring
theorem _root_.solution (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P) : Us c ≤ g * P := by
  unfold Us
  rw [Fintype.sum_prod_type]
  calc ∑ a, ∑ b, c a b ≤ ∑ _a : ι, P := sum_le_sum fun a _ => hP a
    _ = g * P := by simp
end Groundwork.Colouring
