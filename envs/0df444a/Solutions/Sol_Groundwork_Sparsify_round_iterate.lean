-- Prove2me | solution 1 for Groundwork.Sparsify.round_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:54.458193+00:00
-- url     : https://prove2.me/submissions/f2f34aac-3497-4d05-ad72-47e12a98a627

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree
import Theorems.Thm_Groundwork_Sparsify_leaves_length_pos

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
namespace Groundwork.Sparsify
theorem _root_.solution (k : ℕ) (s : σ) (hk : ∀ x ∈ leaves step k s, step x = none) (r out : List σ) :
    (round step)^[2 * (leaves step k s).length - 1] (s :: r, out) = (r, (leaves step k s).reverse ++ out) := by
  induction k generalizing s r out with
  | zero =>
    have h0 : step s = none := hk s (by simp [leaves])
    simp [leaves, round, h0]
  | succ k ih =>
    cases h0 : step s with
    | none => simp [leaves, round, h0]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      have e0 : leaves step (k + 1) s = leaves step k l ++ leaves step k h := by simp [leaves, h0]
      rw [e0] at hk ⊢
      have hl := leaves_length_pos step k l
      have hh := leaves_length_pos step k h
      have e : 2 * (leaves step k l ++ leaves step k h).length - 1 =
          (2 * (leaves step k h).length - 1) + ((2 * (leaves step k l).length - 1) + 1) := by
        simp only [List.length_append]; omega
      rw [e, Function.iterate_add_apply, Function.iterate_succ_apply]
      have e1 : round step (s :: r, out) = (l :: h :: r, out) := by simp [round, h0]
      rw [e1, ih l (fun x hx => hk x (List.mem_append_left _ hx)),
        ih h (fun x hx => hk x (List.mem_append_right _ hx))]
      simp
end Groundwork.Sparsify
