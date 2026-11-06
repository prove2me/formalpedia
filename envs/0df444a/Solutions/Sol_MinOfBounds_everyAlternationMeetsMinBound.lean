-- Prove2me | solution 1 for MinOfBounds.everyAlternationMeetsMinBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:36:03.694094+00:00
-- url     : https://prove2.me/submissions/dd4cd8fc-88a3-4d58-bf2c-7ea7dab75957

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_TwoMachines_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_MinOfBounds_Main
import Theorems.Thm_MinOfBounds_alternation_outputs

set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : EveryAlternationMeetsMinBound := fun _ hpre _ _ h₁ _ _ h₂ _ _ hN => alternation_outputs hpre h₁ h₂ hN
end MinOfBounds
