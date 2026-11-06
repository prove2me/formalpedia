-- Prove2me | solution 1 for GraphProblems.Color.asg_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:31.923935+00:00
-- url     : https://prove2.me/submissions/1d7cbb26-3f0d-4bf4-b052-8ed82dccf0dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
import Theorems.Thm_GraphProblems_Color_ext_asg

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks
namespace GraphProblems.Color
theorem _root_.solution {n k : ℕ} : Function.Injective (asg : (Fin n → Fin k) → Fin (n * k) → Bool) := by
  intro col col' h
  funext v
  have h1 := ext_asg col v (col v).2
  rw [h, ext_asg col' v (col v).2, decide_eq_true (rfl : (col v).val = (col v).val)] at h1
  exact (Fin.ext (of_decide_eq_true h1)).symm
end GraphProblems.Color
