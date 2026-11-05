-- Prove2me | solution 1 for Groundwork.Prog.Count.exists_idx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:22.805881+00:00
-- url     : https://prove2.me/submissions/c51e2d76-2f78-4e79-9096-b92c9914f6d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_exists_loc
import Theorems.Thm_Groundwork_Prog_Count_idx_eq
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
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
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
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
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution {i : ℕ} (h : i < g * μ * k) : ∃ p : Slot g μ k, idx p = i := by
  rw [Nat.mul_assoc] at h
  have hn : 0 < μ * k := by
    rcases Nat.eq_zero_or_pos (μ * k) with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  obtain ⟨s, hs⟩ := exists_loc (μ := μ) (k := k) (Nat.mod_lt i hn)
  refine ⟨(⟨i / (μ * k), Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩, s), ?_⟩
  rw [idx_eq, hs]
  exact Nat.div_add_mod' i (μ * k)
end Groundwork.Prog.Count
