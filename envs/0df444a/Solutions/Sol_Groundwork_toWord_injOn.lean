-- Prove2me | solution 1 for Groundwork.toWord_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:38:52.024424+00:00
-- url     : https://prove2.me/submissions/66540d9a-6443-415a-a1ee-7cbb580ca248

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
import Theorems.Thm_Groundwork_ofWord_toWord

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution (ℓ : ℕ) : Set.InjOn (toWord ℓ) (range (2 ^ ℓ) : Finset ℕ) := by
  intro y hy y' hy' h
  rw [← ofWord_toWord (mem_range.1 hy), h, ofWord_toWord (mem_range.1 hy')]
end Groundwork
