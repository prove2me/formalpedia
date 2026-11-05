-- Prove2me | solution 1 for Groundwork.Stepped.Reaches.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:20:17.018732+00:00
-- url     : https://prove2.me/submissions/81a6a9fa-2c43-4fe9-8e31-212c2af70b70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
namespace Reaches
theorem _root_.solution {M : Stepped α β} {S S' t t' : ℕ} {b : β} {s : M.σ} (h : M.Reaches S b s t)
    (ht : t ≤ t') (hS : S ≤ S') : M.Reaches S' b s t' := by
  induction h generalizing t' with
  | halt ho hs => exact .halt ho (hs.trans hS)
  | step ho hs _ ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    exact .step ho (hs.trans hS) (ih (by omega))
end Reaches
end Groundwork.Stepped
