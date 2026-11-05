-- Prove2me | solution 1 for Groundwork.Grid.boole_and3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:20.954284+00:00
-- url     : https://prove2.me/submissions/9ca1822c-ba09-4e00-bf4b-1fd5e2d42752

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {S A B C : Prop} {_ : Decidable S} {_ : Decidable A} {_ : Decidable B} {_ : Decidable C}
    (h : S ↔ (A ∧ B) ∧ C) :
    (if S then (1 : ℤ) else 0) = (if A then 1 else 0) * (if B then 1 else 0) * (if C then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [h, hA, hB, hC]
end Groundwork.Grid
