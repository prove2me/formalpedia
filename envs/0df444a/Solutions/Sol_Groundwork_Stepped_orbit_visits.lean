-- Prove2me | solution 1 for Groundwork.Stepped.orbit_visits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:27.972614+00:00
-- url     : https://prove2.me/submissions/24176f39-f6fd-493e-8ab1-0cd8cfe620a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
variable (step : ν → Option (ν × ν))
namespace Groundwork.Stepped
theorem _root_.solution (k : ℕ) (s : ν) (r : List ν) (ys : List (List ν))
    (hk : ∀ x ∈ leaves step k s, step x = none) (h : Orbit (walkNext step) (some r) ys) :
    Orbit (walkNext step) (some (s :: r)) (visits step k s r ++ ys) := by
  induction k generalizing s r ys with
  | zero =>
    have h0 : step s = none := hk s (by simp [leaves])
    have e : walkNext step (s :: r) = some r := by simp [walkNext, h0]
    exact .cons (by rw [e]; exact h)
  | succ k ih =>
    cases h0 : step s with
    | none =>
      have e : walkNext step (s :: r) = some r := by simp [walkNext, h0]
      have ev : visits step (k + 1) s r = [s :: r] := by simp [visits, h0]
      rw [ev]
      exact .cons (by rw [e]; exact h)
    | some lh =>
      obtain ⟨l, h'⟩ := lh
      have e : walkNext step (s :: r) = some (l :: h' :: r) := by simp [walkNext, h0]
      have ev : visits step (k + 1) s r = (s :: r) :: (visits step k l (h' :: r) ++ visits step k h' r) := by
        simp [visits, h0]
      have el : leaves step (k + 1) s = leaves step k l ++ leaves step k h' := by simp [leaves, h0]
      rw [el] at hk
      rw [ev, List.cons_append, List.append_assoc]
      refine .cons ?_
      rw [e]
      exact ih l (h' :: r) _ (fun x hx => hk x (List.mem_append_left _ hx))
        (ih h' r ys (fun x hx => hk x (List.mem_append_right _ hx)) h)
end Groundwork.Stepped
