-- Prove2me | solution 1 for MinOfBounds.theTwoTheoremsImplyMinBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:06.710705+00:00
-- url     : https://prove2.me/submissions/58546b9c-d6a1-47bb-ab37-f7cf32be1486

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
import Theorems.Thm_MinOfBounds_propositionsUnfold
import Theorems.Thm_MinOfBounds_boundInMSuffices
import Theorems.Thm_MinOfBounds_minBoundFromTheTwoTheorems

set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : TheTwoTheoremsImplyMinBound := by
  intro hA hD
  obtain ⟨M₁, C, hf₁, hM₁⟩ := propositionsUnfold.1.1 hA
  obtain ⟨M₂, C₂, hf₂, h₂⟩ := propositionsUnfold.2.1.1 hD
  obtain ⟨C₁, h₁⟩ := boundInMSuffices M₁ C hM₁
  obtain ⟨⟨pre, -, -, N, -, q, -, hpre, hfin, -, halt⟩, hall⟩ := minBoundFromTheTwoTheorems M₁ C₁ hf₁ h₁ M₂ C₂ hf₂ h₂
  obtain ⟨C', hC'⟩ := hall pre hpre N q halt
  exact propositionsUnfold.2.2.2 ⟨N, C', hfin, hC'⟩
end MinOfBounds
