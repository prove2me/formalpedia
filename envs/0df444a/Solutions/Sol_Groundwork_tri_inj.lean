-- Prove2me | solution 1 for Groundwork.tri_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:02.16964+00:00
-- url     : https://prove2.me/submissions/0264ce11-87f4-40d0-abde-9030ce6ffe84

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
import Theorems.Thm_Groundwork_tri_zero_succ
import Theorems.Thm_Groundwork_tri_zero_mono
import Theorems.Thm_Groundwork_tri_eq

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {a b a' b' : ℕ} (hab : a < b) (hab' : a' < b') (h : tri a b = tri a' b') :
    a = a' ∧ b = b' := by
  rw [tri_eq a b, tri_eq a' b'] at h
  rcases lt_trichotomy b b' with hb | hb | hb
  · have h1 := tri_zero_succ b
    have h2 := tri_zero_mono (show b + 1 ≤ b' from hb)
    omega
  · subst hb; exact ⟨by omega, rfl⟩
  · have h1 := tri_zero_succ b'
    have h2 := tri_zero_mono (show b' + 1 ≤ b from hb)
    omega
end Groundwork
