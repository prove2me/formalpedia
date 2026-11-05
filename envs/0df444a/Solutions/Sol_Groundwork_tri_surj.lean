-- Prove2me | solution 1 for Groundwork.tri_surj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:59.761034+00:00
-- url     : https://prove2.me/submissions/ef02d0b4-cfb8-4f14-a4d0-aa9954a84360

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_tri_zero_succ
import Theorems.Thm_Groundwork_tri_eq
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {K j : ℕ} (h : j < K * (K - 1) / 2) : ∃ a b, a < b ∧ b < K ∧ tri a b = j := by
  have h3 : ∀ K, tri 0 K = K * (K - 1) / 2 := fun K => by simp [tri]
  rw [← h3] at h
  induction K with
  | zero => simp [tri] at h
  | succ K ih =>
    rw [tri_zero_succ] at h
    by_cases hj : j < tri 0 K
    · obtain ⟨a, b, h1, h2, h3⟩ := ih hj
      exact ⟨a, b, h1, by omega, h3⟩
    · exact ⟨j - tri 0 K, K, by omega, by omega, by rw [tri_eq]; omega⟩
end Groundwork
