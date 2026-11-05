-- Prove2me | solution 1 for Groundwork.Stepped.ofOption_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:26:39.052175+00:00
-- url     : https://prove2.me/submissions/56ae6513-32ca-46b8-9985-84342e7b5710

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb

set_option autoImplicit false
section
section
open Groundwork Groundwork.Stepped
variable {α β : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] [HasSize β] {g : α → Option β} {a : α} {b : β} (h : g a = some b) :
    (ofOption g).Runs a 1 (max (size a) (size b) + 1) b :=
  .step rfl (by change size a + 1 ≤ _; omega) (by
    have e : (ofOption g).step (.inl a) = .inr b := by change (match g a with | some b => _ | none => _) = _; rw [h]
    rw [show (ofOption g).init a = .inl a from rfl, e]
    exact .halt rfl (by change size b + 1 ≤ _; omega))
end Groundwork.Stepped
