-- Prove2me | solution 1 for Groundwork.ofWord_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:30:57.850959+00:00
-- url     : https://prove2.me/submissions/2acca1e6-4dab-4afe-a9c3-f4e30048917f

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
theorem _root_.solution (w : List Bool) : ofWord w < 2 ^ w.length := by
  induction w with
  | nil => simp [ofWord]
  | cons b w ih =>
    have : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [ofWord, List.length_cons, pow_succ]
    omega
end Groundwork
