-- Prove2me | solution 1 for MinOfBounds.minBoundFromTheTwoTheorems
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:21.43725+00:00
-- url     : https://prove2.me/submissions/cefdcb5f-39b1-45f1-a194-a55375dbefff

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
import Theorems.Thm_MinOfBounds_everyAlternationMeetsMinBound
import Theorems.Thm_MinOfBounds_renamingFrontEndExists
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_TwoMachines_everyTwoMachinesCanBeAlternated
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : MinBoundFromTheTwoTheorems := by
  intro M₁ C₁ hf₁ h₁ M₂ C₂ hf₂ h₂
  obtain ⟨pre, hpoly, hpre⟩ := renamingFrontEndExists
  obtain ⟨K₁, K₂, N, q₀, q, hfin, hhost, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ pre pre id id hpoly hpoly PolyT.id' PolyT.id'
  exact ⟨⟨pre, K₁, K₂, N, q₀, q, hpoly, hpre, hfin, hhost, halt⟩, fun pre hpre N q hN => everyAlternationMeetsMinBound pre hpre M₁ C₁ h₁ M₂ C₂ h₂ N q hN⟩
end MinOfBounds
