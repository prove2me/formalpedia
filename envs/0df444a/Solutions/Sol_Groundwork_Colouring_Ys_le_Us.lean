-- Prove2me | solution 1 for Groundwork.Colouring.Ys_le_Us
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:58.125969+00:00
-- url     : https://prove2.me/submissions/fac5a190-fecb-4bab-86b4-59a8b1bf7acc

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
omit [DecidableEq ι] [Fintype κ]
namespace Groundwork.Colouring
theorem _root_.solution (γ γ' : κ) (χ : ι → κ) : Ys c γ γ' χ ≤ Us c := by
  unfold Ys Us
  refine sum_le_sum fun p _ => ?_
  split_ifs <;> simp
end Groundwork.Colouring
