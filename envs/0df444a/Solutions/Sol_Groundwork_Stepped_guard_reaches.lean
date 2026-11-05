-- Prove2me | solution 1 for Groundwork.Stepped.guard_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:55.817195+00:00
-- url     : https://prove2.me/submissions/b3e3ca6a-4356-44fb-8d71-fa3361129987

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
namespace Groundwork.Stepped
theorem _root_.solution {sel : τ → Option ν} {T : Stepped ν β} {d b : β} {s : T.σ} {t S : ℕ}
    (h : T.Reaches S b s t) : (guard sel T d).Reaches (S + 1) b (some s) t := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho hs _ ih => exact .step ho (Nat.succ_le_succ hs) ih
end Groundwork.Stepped
