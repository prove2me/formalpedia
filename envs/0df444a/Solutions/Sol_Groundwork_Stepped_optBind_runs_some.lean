-- Prove2me | solution 1 for Groundwork.Stepped.optBind_runs_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:13.235465+00:00
-- url     : https://prove2.me/submissions/f5505959-5726-4a1d-8762-19b34c38350b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
import Theorems.Thm_Groundwork_Stepped_branch_runs_inl
import Theorems.Thm_Groundwork_Stepped_bind_runs


set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] [HasSize β] {M : Stepped α (Option ι)} {N : Stepped (α × ι) β}
    {dflt : α → β} {a : α} {i : ι} {t t' S S' : ℕ} {b : β} (h : M.Runs a t S (some i))
    (h' : N.Runs (a, i) t' S' b) : (optBind M N dflt).Runs a (t + 1 + t') (max (size a + S) (S' + 1) + 1) b :=
  bind_runs h (branch_runs_inl rfl h')
end Groundwork.Stepped
