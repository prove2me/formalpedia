-- Prove2me | solution 1 for Groundwork.tri_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:00.893463+00:00
-- url     : https://prove2.me/submissions/4be1b8ea-fd52-4c59-ac7c-a04883862e85

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
import Theorems.Thm_Groundwork_tri_zero_mono
import Theorems.Thm_Groundwork_tri_eq
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {a b K : ℕ} (hab : a < b) (hb : b < K) : tri a b < K * (K - 1) / 2 := by
  have h1 := tri_zero_succ b
  have h2 := tri_zero_mono (show b + 1 ≤ K from hb)
  have h3 : tri 0 K = K * (K - 1) / 2 := by simp [tri]
  rw [tri_eq]; omega
end Groundwork
