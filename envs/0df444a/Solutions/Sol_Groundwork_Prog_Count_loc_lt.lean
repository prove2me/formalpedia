-- Prove2me | solution 1 for Groundwork.Prog.Count.loc_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:40:50.815717+00:00
-- url     : https://prove2.me/submissions/eee3cf5b-ac9c-4fa9-9ef0-3988959d8891

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (s : Sl μ k) : loc s < μ * k := by
  have h1 : (s.1.val + 1) * k ≤ μ * k := Nat.mul_le_mul_right k s.1.2
  have := s.2.2
  rw [Nat.succ_mul] at h1
  unfold loc
  omega
end Groundwork.Prog.Count
