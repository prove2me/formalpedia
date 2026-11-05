-- Prove2me | solution 1 for Groundwork.Prog.prod_counter_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:11:04.321305+00:00
-- url     : https://prove2.me/submissions/2bff7ca5-a9f5-4c28-aaa1-c1a6fb01dd0e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
import Definitions.Def_StepMachines_Prog_SidePresents

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
namespace Groundwork.Prog
theorem _root_.solution (g : ℕ) (F : ℕ → ℕ → ℤ) :
    ∏ j ∈ range (g * g), (if j / g < j % g then F (j / g) (j % g) else 1) =
      ∏ k : Fin g × Fin g with k.1 < k.2, F k.1 k.2 := by
  rw [Finset.prod_filter, Finset.prod_range, ← Equiv.prod_comp finProdFinEquiv]
  refine Finset.prod_congr rfl ?_
  rintro ⟨a, b⟩ -
  have hg : 0 < g := a.pos
  have hy : (finProdFinEquiv (a, b)).val = b.val + g * a.val := rfl
  have h1 : (b.val + g * a.val) / g = a.val := by
    rw [Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt b.2, Nat.zero_add]
  have h2 : (b.val + g * a.val) % g = b.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.2]
  rw [hy, h1, h2]
  rfl
end Groundwork.Prog
