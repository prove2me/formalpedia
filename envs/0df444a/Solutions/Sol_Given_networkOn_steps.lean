-- Prove2me | solution 1 for Given.networkOn_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:49.081039+00:00
-- url     : https://prove2.me/submissions/d3627ea5-7d74-442b-8707-aeca4fb02c83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Printed_networkOn_poly


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
namespace Given
theorem _root_.solution {Q A C : Type} [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) (hN : NM.PolyTimeSteps) (h : PolyTimeProcs Np) : (networkOn g NM Np).PolyTimeSteps :=
  networkOn_poly g NM Np hN h.P h.B h.len h.cap h.mem h.W h.Ψ h.f
end Given
