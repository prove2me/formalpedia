-- Prove2me | solution 1 for Groundwork.Host.size_le_of_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:18.788189+00:00
-- url     : https://prove2.me/submissions/74c34998-9c61-4d69-bdf5-10cd521189ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host

set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
variable {M : Stepped (List Bool) Bool}
namespace Groundwork.Host
theorem _root_.solution {S t : ℕ} {b : Bool} {s : M.σ} (h : M.Reaches S b s t) : size s ≤ S := by
  cases h with
  | halt _ hs => exact hs
  | step _ hs _ => exact hs
end Groundwork.Host
