-- Prove2me | solution 1 for Groundwork.Colouring.cheb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:36.371247+00:00
-- url     : https://prove2.me/submissions/df37fab1-9f25-4be1-acb7-90269ba99e8b

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
namespace Groundwork.Colouring
theorem _root_.solution {Ω : Type*} [Fintype Ω] (f : Ω → ℤ) (s : ℤ) (hs : 0 ≤ s) :
    (#{χ : Ω | s ≤ f χ} : ℤ) * s ^ 2 ≤ ∑ χ, f χ ^ 2 := by
  calc (#{χ : Ω | s ≤ f χ} : ℤ) * s ^ 2 = ∑ χ with s ≤ f χ, s ^ 2 := by
        simp [sum_const]
    _ ≤ ∑ χ with s ≤ f χ, f χ ^ 2 :=
        sum_le_sum fun χ h => pow_le_pow_left₀ hs (mem_filter.1 h).2 2
    _ ≤ ∑ χ, f χ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
end Groundwork.Colouring
