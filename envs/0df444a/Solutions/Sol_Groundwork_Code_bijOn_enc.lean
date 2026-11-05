-- Prove2me | solution 1 for Groundwork.Code.bijOn_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:23.600504+00:00
-- url     : https://prove2.me/submissions/ec91c8ed-e114-4e1b-aded-5aa2396e0c14

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
import Theorems.Thm_Groundwork_Code_enc_dec

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution (c : Code S n) : Set.BijOn c.enc S c.D := by
  refine ⟨fun x hx => mem_coe.2 (c.enc_mem (mem_coe.1 hx)), fun x hx x' hx' h => ?_, fun w hw => ?_⟩
  · rw [← c.dec_enc (mem_coe.1 hx), h, c.dec_enc (mem_coe.1 hx')]
  · exact ⟨c.dec w, c.bij.mapsTo hw, c.enc_dec (mem_coe.1 hw)⟩
end Groundwork.Code
