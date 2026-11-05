-- Prove2me | solution 1 for Groundwork.Prog.Count.boole_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:31:26.996709+00:00
-- url     : https://prove2.me/submissions/356386c4-64a5-4fc7-a631-f7595c8bdea6

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
theorem _root_.solution {P Q : Prop} {_ : Decidable P} {_ : Decidable Q} (h : P ↔ Q) :
    (if P then (1 : ℤ) else 0) = if Q then 1 else 0 := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg fun hq => hp (h.2 hq)]
end Groundwork.Prog.Count
