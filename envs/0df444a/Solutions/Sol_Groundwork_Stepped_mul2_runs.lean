-- Prove2me | solution 1 for Groundwork.Stepped.mul2_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:14.381094+00:00
-- url     : https://prove2.me/submissions/d26ae640-7fe7-4fc5-b6a2-3653013548b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
import Theorems.Thm_Groundwork_Stepped_map2_runs

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] {M N : Stepped α ℤ} {a : α} {t t' S S' : ℕ} {b c : ℤ}
    (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (mul2 M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (b * c) :=
  map2_runs h h'
end Groundwork.Stepped
