-- Prove2me | solution 1 for Given.stEveryEta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:02:19.399063+00:00
-- url     : https://prove2.me/submissions/1de0e8cd-6396-43f0-86ac-4c62f80c5554

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_eStarZero
import Theorems.Thm_Printed_eStarZero
import Theorems.Thm_Printed_stEveryEta_of


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : StEveryEta := stEveryEta_of eStarZero
end Given
