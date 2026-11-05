-- Prove2me | solution 1 for Groundwork.Stepped.both_reaches_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:46:08.306177+00:00
-- url     : https://prove2.me/submissions/99118709-41ac-4719-adaf-efa7d383a397

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] [HasSize β] {M : Stepped α β} {N : Stepped α γ} {S t : ℕ} {b : β} {c : γ}
    {s : N.σ} (h : N.Reaches S c s t) : (both M N).Reaches (size b + S + 1) (b, c) (.inr (b, s)) t := by
  induction h with
  | @halt s t ho hs =>
    exact .halt (by change (N.out s).map _ = _; rw [ho]; rfl) (by change size b + size s + 1 ≤ _; omega)
  | @step s t ho hs _ ih =>
    exact .step (by change (N.out s).map _ = _; rw [ho]; rfl) (by change size b + size s + 1 ≤ _; omega) ih
end Groundwork.Stepped
