-- Prove2me | solution 1 for Groundwork.Stepped.walk_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:27:50.632947+00:00
-- url     : https://prove2.me/submissions/e63b6444-abcd-4a29-8def-ab0c26672aa3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
import Theorems.Thm_Groundwork_Stepped_guard_runs_none
import Theorems.Thm_Groundwork_Stepped_guard_runs_some
import Theorems.Thm_Groundwork_Stepped_foldl_or_sel
import Theorems.Thm_Groundwork_Stepped_sum_sel
import Theorems.Thm_Groundwork_Stepped_orbit_visits
import Theorems.Thm_Groundwork_Stepped_length_visits
import Theorems.Thm_Groundwork_Stepped_filterMap_visits
import Theorems.Thm_Groundwork_Stepped_exists_round_of_orbit
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_foldWhile_runs
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
theorem _root_.solution [HasSize ν] {root : α → ν} {T : Stepped ν Bool} (k : ℕ) (a : α)
    (hk : ∀ x ∈ leaves step k (root a), step x = none) (v : ν → Bool) (t Sm Sx : ℕ)
    (hT : ∀ x ∈ leaves step k (root a), T.Runs x t Sm (v x))
    (hS : ∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx) :
    (walk step root T).Runs a ((leaves step k (root a)).length * (t + 2)) (Sx + (1 + (Sm + 1)) + 1)
      ((leaves step k (root a)).any v) := by
  have ho : Orbit (walkNext step) (some [root a]) (visits step k (root a) [] ++ [[]]) :=
    orbit_visits step k (root a) [] [[]] hk (.cons .nil)
  have hf : (visits step k (root a) [] ++ [[]]).filterMap (walkSel step) = leaves step k (root a) := by
    rw [List.filterMap_append, filterMap_visits step k (root a) [] hk]
    simp [walkSel]
  have hlen : (visits step k (root a) [] ++ [[]]).length = 2 * (leaves step k (root a)).length := by
    rw [List.length_append, ← length_visits step k (root a) []]
    rfl
  have key := foldWhile_runs (start := fun a : α => some [root a]) (M := guard (walkSel step) T false)
    (g := fun c _ b => c || b) (c₀ := fun _ => false) (a := a) ho
    (fun st => ((walkSel step st).map fun _ => t).getD 0) (fun st => ((walkSel step st).map v).getD false)
    Sx 1 (Sm + 1)
    (by
      intro st hst
      cases h : walkSel step st with
      | none => exact (guard_runs_none h).mono le_rfl (by omega)
      | some x => exact guard_runs_some h (hT x (hf ▸ List.mem_filterMap.2 ⟨st, hst, h⟩)))
    (by
      intro st hst
      obtain ⟨i, rfl⟩ := exists_round_of_orbit step ho st hst
      exact hS i)
    (fun _ _ => le_rfl)
  rw [sum_sel, foldl_or_sel, hf, hlen, Bool.false_or] at key
  exact key.mono (le_of_eq (by ring)) le_rfl
end Groundwork.Stepped
