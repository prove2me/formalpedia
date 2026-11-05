-- Prove2me | solution 1 for Groundwork.Sparsify.reduced_red
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:36:34.027292+00:00
-- url     : https://prove2.me/submissions/d175e8a5-b208-4c72-9444-15ea693ec1a2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Nat
import Definitions.Def_StepMachines_Math_Sparsify
import Theorems.Thm_Groundwork_Sparsify_red_subset

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
namespace Groundwork.Sparsify
theorem _root_.solution (F : Finset (Finset α)) : Reduced (red F) := by
  intro C hC D hD h
  exact (mem_filter.1 hC).2 D (red_subset F hD) h
end Groundwork.Sparsify
