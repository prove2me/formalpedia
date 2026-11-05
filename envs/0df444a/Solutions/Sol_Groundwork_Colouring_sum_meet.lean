-- Prove2me | solution 1 for Groundwork.Colouring.sum_meet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:05:20.667729+00:00
-- url     : https://prove2.me/submissions/ef8b2209-d8aa-4f3f-8d88-1617b1e25219

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
namespace Groundwork.Colouring
theorem _root_.solution (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P) (p : ι × ι) :
    ∑ q : ι × ι, c q.1 q.2 * meet p q ≤ 4 * P := by
  have r1 : ∀ x : ι, ∑ q : ι × ι, c q.1 q.2 * (if q.1 = x then 1 else 0) ≤ P := by
    intro x
    rw [Fintype.sum_prod_type, sum_comm]
    simpa using hP x
  have r2 : ∀ x : ι, ∑ q : ι × ι, c q.1 q.2 * (if q.2 = x then 1 else 0) ≤ P := by
    intro x
    rw [Fintype.sum_prod_type]
    have := hP x
    simp only [hs x] at this
    simpa using this
  unfold meet
  simp only [mul_add, sum_add_distrib]
  have := r1 p.1; have := r1 p.2; have := r2 p.1; have := r2 p.2
  omega
end Groundwork.Colouring
