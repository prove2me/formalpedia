-- Prove2me | solution 1 for Groundwork.toWord_ofWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:31:11.321369+00:00
-- url     : https://prove2.me/submissions/e5c2b9ae-9531-4545-8901-0cf2da85b1bf

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
theorem _root_.solution (w : List Bool) : toWord w.length (ofWord w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have h1 : (b.toNat + 2 * ofWord w) / 2 = ofWord w := by
      have : b.toNat ≤ 1 := Bool.toNat_le b
      omega
    simp only [List.length_cons, toWord, ofWord, h1, ih]
    cases b <;> simp
end Groundwork
