-- Prove2me | solution 1 for Groundwork.Prog.Count.nodup_links
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:33.348232+00:00
-- url     : https://prove2.me/submissions/5e394c83-b006-41eb-95b4-2235f4d5cf1f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_locals_eq

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) (a b : ℕ) : (links g k φ a b).Nodup := by
  rw [links, locals_eq hg]
  exact (List.nodup_range.product List.nodup_range).filter _
end Groundwork.Prog.Count
