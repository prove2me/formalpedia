-- Prove2me | solution 1 for Groundwork.Code.sum_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:07:43.514463+00:00
-- url     : https://prove2.me/submissions/1b30aaad-0e51-4843-84c9-62aa61c2dfe7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
import Theorems.Thm_Groundwork_Code_image_dec

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution {M : Type*} [AddCommMonoid M] (c : Code S n) (F : X → M) :
    ∑ w ∈ c.D, F (c.dec w) = ∑ x ∈ S, F x := by
  classical
  conv_rhs => rw [← c.image_dec]
  exact (sum_image c.bij.injOn).symm
end Groundwork.Code
