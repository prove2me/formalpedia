-- Prove2me | solution 1 for Groundwork.ofWord_toWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:26:24.942205+00:00
-- url     : https://prove2.me/submissions/182f0d26-beab-4cff-9995-b29a0a61f73e

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
attribute [local simp] Groundwork.length_toWord

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {ℓ y : ℕ} (h : y < 2 ^ ℓ) : ofWord (toWord ℓ y) = y := by
  induction ℓ generalizing y with
  | zero => simp only [pow_zero] at h; simp only [toWord, ofWord]; omega
  | succ ℓ ih =>
    have h2 : y / 2 < 2 ^ ℓ := by rw [pow_succ] at h; omega
    simp only [toWord, ofWord, ih h2]
    rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;> simp [h'] <;> omega
end Groundwork
