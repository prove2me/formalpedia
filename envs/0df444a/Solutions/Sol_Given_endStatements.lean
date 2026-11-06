-- Prove2me | solution 1 for Given.endStatements
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:24:32.785422+00:00
-- url     : https://prove2.me/submissions/03170b7e-b2ba-41f2-b17b-67f0188000a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_levelProposition
import Theorems.Thm_Given_eStarZero
import Theorems.Thm_Given_stEveryEta
import Theorems.Thm_Given_stClique
import Theorems.Thm_Given_stAlgorithm
import Theorems.Thm_Given_stDecides
import Theorems.Thm_Given_stProofNamed
import Theorems.Thm_Given_threeSat_through_eStar
import Theorems.Thm_Given_threeSat_by_algorithm
import Theorems.Thm_Enumerate_stEnumeration
import Theorems.Thm_Exits_stAlgorithm
import Theorems.Thm_Exits_stClique
import Theorems.Thm_Exits_stDecides
import Theorems.Thm_Exits_stProofNamed
import Theorems.Thm_Exits_threeSat_by_algorithm
import Theorems.Thm_Exits_threeSat_through_eStar
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_eStarZero
import Theorems.Thm_Printed_groupingLemma
import Theorems.Thm_Printed_levelProposition
import Theorems.Thm_Printed_stAlgorithm
import Theorems.Thm_Printed_stAnswerEachQuery
import Theorems.Thm_Printed_stClique
import Theorems.Thm_Printed_stDecides
import Theorems.Thm_Printed_stEveryEta
import Theorems.Thm_Printed_stHalf
import Theorems.Thm_Printed_stMono
import Theorems.Thm_Printed_stProofNamed
import Theorems.Thm_Printed_threeSat_by_algorithm
import Theorems.Thm_Printed_threeSat_through_eStar
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_stMono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : EndStatements where
  mono := stMono
  half := stHalf
  answerEachQuery := stAnswerEachQuery
  groupingLemma := groupingLemma
  levelProposition := levelProposition
  eStarZero := eStarZero
  everyEta := stEveryEta
  clique := stClique
  enumeration := Enumerate.stEnumeration
  proofNamed := stProofNamed
  algorithm := stAlgorithm
  decides := stDecides
  through_eStar := threeSat_through_eStar
  by_algorithm := threeSat_by_algorithm
end Given
