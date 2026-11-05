-- Prove2me | solution 1 for Groundwork.Stepped.foldRange_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:54:44.918605+00:00
-- url     : https://prove2.me/submissions/8f729299-dbf9-417b-9eaa-f6c2fdf2b49d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range
import Theorems.Thm_Groundwork_Stepped_orbit_range
import Theorems.Thm_Groundwork_Stepped_sum_map_range
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
open Finset
variable {α β γ : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] [HasSize γ] {N : α → ℕ} {M : Stepped (α × ℕ) β} {g : γ → ℕ → β → γ}
    {c₀ : α → γ} {a : α} (t : ℕ → ℕ) (v : ℕ → β) (Sc Sm : ℕ) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y))
    (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (foldRange N M g c₀).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (Sc + Sm) + 1)
      ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by
  have ho := orbit_range N a (N a) 0 (by omega)
  rw [← List.range_eq_range'] at ho
  have := foldWhile_runs (start := rangeStart N) (M := M)
    (g := rangeG g) (c₀ := c₀) ho (fun x => t x.2) (fun x => v x.2)
    (size a + size (N a)) Sc Sm
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM y (List.mem_range.1 hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := Nat.size_le_size (List.mem_range.1 hy).le
      simp only [size_prod, size_nat]; omega)
    (by
      intro l hl
      rw [List.prefix_iff_eq_take] at hl
      rw [hl, ← List.map_take, List.take_range, List.foldl_map]
      exact hc _ (min_le_right _ _))
  rw [List.map_map, List.foldl_map] at this
  rw [← sum_map_range]
  exact this
end Groundwork.Stepped
