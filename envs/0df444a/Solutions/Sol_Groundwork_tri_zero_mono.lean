-- Prove2me | solution 1 for Groundwork.tri_zero_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:26.298791+00:00
-- url     : https://prove2.me/submissions/3900d559-4aff-4e3b-9947-a805db97338c

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
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {b b' : ℕ} (h : b ≤ b') : tri 0 b ≤ tri 0 b' := by
  simp only [tri, add_zero]
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))
end Groundwork
