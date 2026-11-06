-- Prove2me | solution 1 for Given.stLevelTied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:58.135867+00:00
-- url     : https://prove2.me/submissions/4408cf2c-2014-4c56-ad70-37b8abf7e600

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Given_levelMachine_achieves
import Theorems.Thm_Printed_stGroupingTied


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
namespace Given
theorem _root_.solution : StLevelTied := by
  intro K e M Cc hK h0 hM
  obtain ⟨C₁, hC⟩ := stGroupingTied K e M Cc hK h0 hM
  have hg : K ≤ 3 * K ^ 8 := by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega
  rw [sq]
  exact levelMachine_achieves hK hg h0 hC
end Given
