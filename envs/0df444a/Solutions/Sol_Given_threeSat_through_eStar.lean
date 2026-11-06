-- Prove2me | solution 1 for Given.threeSat_through_eStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:05.852004+00:00
-- url     : https://prove2.me/submissions/7c6e3706-a51a-4093-b7fd-ca420a87067a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_stEveryEta
import Theorems.Thm_Given_stProofNamed
import Theorems.Thm_Enumerate_stEnumeration
import Theorems.Thm_Exits_stProofNamed
import Theorems.Thm_Printed_stEveryEta
import Theorems.Thm_Printed_stProofNamed
import Theorems.Thm_Printed_threeSat_through_eStar_of


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : Sat3.ThmEveryDelta := threeSat_through_eStar_of stEveryEta Enumerate.stEnumeration stProofNamed
end Given
