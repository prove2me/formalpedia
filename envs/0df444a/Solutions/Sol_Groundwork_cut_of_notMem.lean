-- Prove2me | solution 1 for Groundwork.cut_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:23.947748+00:00
-- url     : https://prove2.me/submissions/e3d2d03d-f884-4813-a2e7-3308c5d758e3

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

set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι : Type*} [DecidableEq ι]
namespace Groundwork
theorem _root_.solution (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) {i : ι} (h : i ∉ e) :
    cut c d e w i = d := by
  induction e generalizing w with
  | nil => rfl
  | cons j e ih =>
    rw [List.mem_cons, not_or] at h
    rw [cut, Function.update_of_ne h.1, ih _ h.2]
end Groundwork
