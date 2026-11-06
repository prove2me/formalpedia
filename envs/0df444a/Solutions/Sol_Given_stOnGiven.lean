-- Prove2me | solution 1 for Given.stOnGiven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:02.233879+00:00
-- url     : https://prove2.me/submissions/d7a6bfae-0695-4e1d-8156-f01cf0f225f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GivenStatement
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Given_Networks
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Printed_networkOn_close
import Theorems.Thm_Printed_networkOn_poly
import Theorems.Thm_Printed_stOnProcedures
import Theorems.Thm_QueryMachines_stClose


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
variable {Q A C : Type}
namespace Given
theorem _root_.solution : StOnGiven := by
  intro NM C₁ g K e hNM Q A C _ _ _ _ _ Np O c N P B τ S h
  refine ⟨fun hN => networkOn_poly g NM Np hN h.2.P h.2.B h.2.len h.2.cap h.2.mem h.2.W h.2.Ψ h.2.f, ?_⟩
  obtain ⟨T, hT1, hT2⟩ := stOnProcedures NM C₁ g K e hNM C (Np.close O) c N P B τ S h.1
  refine ⟨T, (stClose _ _ _ _ _ _ _ _ _ _).1 ?_, hT2⟩
  rw [networkOn_close]
  exact hT1
end Given
