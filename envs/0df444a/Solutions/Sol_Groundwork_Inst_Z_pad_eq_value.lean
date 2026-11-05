-- Prove2me | solution 1 for Groundwork.Inst.Z_pad_eq_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:45:24.975785+00:00
-- url     : https://prove2.me/submissions/9cf3efb3-5935-482b-8879-2aee7fb0674c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_Network_Z_toInst
import Theorems.Thm_Groundwork_Inst_toInst_net

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
namespace Inst
theorem _root_.solution [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    (R : Inst J A) (d : A) (d' : A') (D : Finset A') (dec : A' → A) (h : Set.BijOn dec D Set.univ) :
    (R.pad d D dec).Z d' = (R.net d).value := by
  rw [← Inst.toInst_net]
  exact Network.Z_toInst _ _ _ (fun _ _ _ => by simpa [Inst.net] using h) d'
end Inst
end Groundwork
