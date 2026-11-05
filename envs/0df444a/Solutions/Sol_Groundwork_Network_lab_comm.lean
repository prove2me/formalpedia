-- Prove2me | solution 1 for Groundwork.Network.lab_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:52.047766+00:00
-- url     : https://prove2.me/submissions/3265c070-0d29-4d0e-b83b-7ae28b87cfd1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [LinearOrder J] (N : Network J σ τ) (a b : J) : N.lab a b = N.lab b a := by
  simp [lab, min_comm, max_comm]
end Groundwork.Network
