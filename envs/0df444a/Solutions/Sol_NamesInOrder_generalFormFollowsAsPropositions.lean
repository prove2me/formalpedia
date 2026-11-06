-- Prove2me | solution 1 for NamesInOrder.generalFormFollowsAsPropositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:34:27.752459+00:00
-- url     : https://prove2.me/submissions/ed3fbe44-cb21-49bf-9a00-c44fda83abc1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_NamesInOrder_General
import Theorems.Thm_NamesInOrder_generalFormFollows
import Theorems.Thm_MinOfBounds_renamingFrontEndExists
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_Wrap_everyMachineCanBeWrapped
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork Wrap TwoMachines MainTheoremForms MinOfBounds
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : GeneralFormFollowsAsPropositions := by
  rintro ⟨N, C, hf, hN⟩
  obtain ⟨ren, hrenP, hren⟩ := renamingFrontEndExists
  obtain ⟨N', q, hf', hW⟩ := everyMachineCanBeWrapped N hf ren id hrenP PolyT.id'
  obtain ⟨C', -, h2⟩ := generalFormFollows N C hN ren hren N' q hW
  exact ⟨N', C', hf', h2⟩
end NamesInOrder
