-- Prove2me | solution 1 for MinOfBounds.bothComputeTheSameNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:54.471319+00:00
-- url     : https://prove2.me/submissions/992b7c7f-199d-4ff7-9cf2-50ceaa30d903

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
import Theorems.Thm_MinOfBounds_renamedCodeIsTheCodeOfARenaming


set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : BothComputeTheSameNumber := by
  intro M₁ C₁ h₁ M₂ C₂ h₂ k V φ hk hφ hm hn
  obtain ⟨φ', hcode, -, -, -, hlen, hK, hocc, hnum⟩ := renamedCodeIsTheCodeOfARenaming k V φ
  have a₁ := h₁ k (numOcc φ) φ' hk (hK hφ) (hlen ▸ hm) hocc
  have a₂ := h₂ k (numOcc φ) φ' hk hn (hK hφ)
  unfold CountsWithin at a₁ a₂
  rw [hnum, ← hcode] at a₁ a₂
  rw [hlen] at a₁
  exact ⟨a₁, a₂⟩
end MinOfBounds
