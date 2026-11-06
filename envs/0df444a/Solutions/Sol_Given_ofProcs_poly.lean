-- Prove2me | solution 1 for Given.ofProcs_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:33.981401+00:00
-- url     : https://prove2.me/submissions/8067ab7d-4892-4c9c-8472-3dee7257f0c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GivenStatement
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Given_Networks
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
variable {Q A C : Type}
namespace Given
theorem _root_.solution [Enc C] (Np : Procs C) (h : Np.Keeps) (hP : Unary Np.P) (hB : Unary Np.B) : PolyTimeProcs (ofProcs Np) := by
  obtain ⟨i1⟩ := h.mem
  obtain ⟨i2⟩ := h.W
  obtain ⟨i3⟩ := h.Ψ
  obtain ⟨i4⟩ := h.f
  exact ⟨hP, hB, h.len, h.cap, ⟨IsPolyQ.lift _⟩, ⟨IsPolyQ.lift _⟩, ⟨IsPolyQ.lift _⟩, ⟨IsPolyQ.lift _⟩⟩
end Given
