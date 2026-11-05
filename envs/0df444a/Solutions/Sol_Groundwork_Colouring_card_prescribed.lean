-- Prove2me | solution 1 for Groundwork.Colouring.card_prescribed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:46:09.879683+00:00
-- url     : https://prove2.me/submissions/fd514eba-4376-423c-bcd0-0400a184fd5e

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
theorem _root_.solution (S : Finset ι) (f : ι → κ) :
    #{χ : ι → κ | ∀ a ∈ S, χ a = f a} * K ^ #S = N := by
  have h : ({χ : ι → κ | ∀ a ∈ S, χ a = f a} : Finset (ι → κ)) =
      Fintype.piFinset (fun a => if a ∈ S then {f a} else univ) := by
    ext χ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun a => ?_
    split_ifs with h <;> simp [h]
  rw [h, Fintype.card_piFinset]
  have h1 : ∀ a, #(if a ∈ S then {f a} else (univ : Finset κ)) = if a ∈ S then 1 else K := by
    intro a; split_ifs <;> simp
  simp only [h1]
  have h2 : K ^ #S = ∏ a : ι, if a ∈ S then K else 1 := by
    rw [Finset.prod_ite_mem, univ_inter, prod_const]
  rw [h2, ← prod_mul_distrib, ← card_univ (α := ι), ← prod_const]
  refine prod_congr rfl fun a _ => ?_
  split_ifs <;> simp
end Groundwork.Colouring
