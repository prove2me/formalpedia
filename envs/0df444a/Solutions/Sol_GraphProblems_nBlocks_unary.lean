-- Prove2me | solution 1 for GraphProblems.nBlocks_unary
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:39:17.750128+00:00
-- url     : https://prove2.me/submissions/5194b0af-de7d-4d2a-ab2d-93e1947b195d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_CountKSat_Poly
import Definitions.Def_GraphProblems_Cert
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.div
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat
variable {α : Type} [Enc α]

theorem solution (b : ℕ) {n : α → ℕ} (hn : Unary n) : Unary fun a => nBlocks b (n a) := by
  unfold nBlocks
  exact Unary.of_le (hn.add (Unary.const 1)) (by have := hn.poly; fun_prop)
    fun a => Nat.add_le_add_right (Nat.div_le_self _ _) 1
