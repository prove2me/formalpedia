-- Prove2me | solution 1 for MinOfBounds.everyAlternationDecidesWithinMinBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:36:39.581947+00:00
-- url     : https://prove2.me/submissions/0ce8580f-2eda-430d-a48f-d92cfcc15aff

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
import Theorems.Thm_VariableBound_Paper_numSatOcc_lt
import Theorems.Thm_VariableBound_Paper_satisfiable_iff
import Theorems.Thm_VariableBound_Rename_anyBit_binary


set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : EveryAlternationDecidesWithinMinBound := by
  intro pre hpre M₁ C₁ h₁ M₂ C₂ h₂ N q hN
  obtain ⟨C, hC⟩ := alternation_outputs hpre h₁ h₂ hN
  refine ⟨C, fun k V φ hk hφ hm hn => ⟨decide (numSatOcc φ ≠ 0), by rw [decide_eq_true_iff, VariableBound.Paper.satisfiable_iff], ?_⟩⟩
  have h := hC k V φ hk hφ hm hn
  have e : someBit (SatK.binary (numOcc φ) (numSatOcc φ)) = [decide (numSatOcc φ ≠ 0)] := VariableBound.Rename.anyBit_binary (VariableBound.Paper.numSatOcc_lt φ)
  rw [e] at h
  exact h
end MinOfBounds
