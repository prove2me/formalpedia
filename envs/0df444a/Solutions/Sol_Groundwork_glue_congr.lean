-- Prove2me | solution 1 for Groundwork.glue_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:25.126204+00:00
-- url     : https://prove2.me/submissions/02e8f9bf-b17c-425c-bd29-d12f3d9c64fa

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
omit [DecidableEq ι]
namespace Groundwork
theorem _root_.solution (e : List ι) {t t' : ι → List Bool} (h : ∀ i ∈ e, t i = t' i) : glue e t = glue e t' := by
  unfold glue; rw [List.map_congr_left h]
end Groundwork
