-- Prove2me | solution 1 for Groundwork.Code.sum_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:10.8052+00:00
-- url     : https://prove2.me/submissions/813db3e5-3c4e-4c48-a6cb-406ffaeb2eec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
import Theorems.Thm_Groundwork_Code_D_subset
import Theorems.Thm_Groundwork_Code_sum_dec

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution {M : Type*} [AddCommMonoid M] (c : Code S n) (F : X → M) :
    ∑ w ∈ words n, (if w ∈ c.D then F (c.dec w) else 0) = ∑ x ∈ S, F x := by
  rw [sum_ite_mem, inter_eq_right.2 c.D_subset, c.sum_dec]
end Groundwork.Code
