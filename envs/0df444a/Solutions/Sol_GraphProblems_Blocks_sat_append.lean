-- Prove2me | solution 1 for GraphProblems.Blocks.sat_append
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:36:55.57959+00:00
-- url     : https://prove2.me/submissions/4e3d96e6-497f-4844-bf45-45f515808f51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_GraphProblems_Blocks
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Blocks

theorem solution (f : ℕ → Bool) (φ χ : Fml) : Sat f (φ ++ χ) ↔ Sat f φ ∧ Sat f χ := by
  simp only [Sat, List.mem_append, or_imp, forall_and]
