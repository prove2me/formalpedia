-- Prove2me | solution 1 for Groundwork.Stepped.map2_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:20.028715+00:00
-- url     : https://prove2.me/submissions/f007842e-635f-4008-9c93-1170bf754c52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
import Theorems.Thm_Groundwork_Stepped_both_runs
import Theorems.Thm_Groundwork_Stepped_mapOut_runs


set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] [HasSize β] {f : β → γ → δ} {M : Stepped α β} {N : Stepped α γ} {a : α}
    {t t' S S' : ℕ} {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (map2 f M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (f b c) :=
  mapOut_runs (both_runs h h')
end Groundwork.Stepped
