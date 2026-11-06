-- Prove2me | solution 1 for MinOfBounds.decidingFromTheTwoTheorems
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:58.89599+00:00
-- url     : https://prove2.me/submissions/ed53d7f8-ada3-4168-984f-a58579aa13fa

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
import Theorems.Thm_MinOfBounds_everyAlternationDecidesWithinMinBound
import Theorems.Thm_MinOfBounds_renamingFrontEndExists
import Theorems.Thm_TwoMachines_everyTwoMachinesCanBeAlternated
import Theorems.Thm_VariableBound_Rename_anyBit_polyT


set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : DecidingFromTheTwoTheorems := by
  intro M₁ C₁ hf₁ h₁ M₂ C₂ hf₂ h₂
  obtain ⟨pre, hpoly, hpre⟩ := renamingFrontEndExists
  have hs : PolyT someBit := VariableBound.Rename.anyBit_polyT
  obtain ⟨K₁, K₂, N, q₀, q, hfin, hhost, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ pre pre someBit someBit hpoly hpoly hs hs
  exact ⟨⟨pre, K₁, K₂, N, q₀, q, hpoly, hpre, hfin, hhost, halt⟩, fun pre hpre N q hN => everyAlternationDecidesWithinMinBound pre hpre M₁ C₁ h₁ M₂ C₂ h₂ N q hN⟩
end MinOfBounds
