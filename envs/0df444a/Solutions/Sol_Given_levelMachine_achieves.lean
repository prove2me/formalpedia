-- Prove2me | solution 1 for Given.levelMachine_achieves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:38.775201+00:00
-- url     : https://prove2.me/submissions/9be52d7f-a4c3-4f6c-a86c-851d877957c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Given_level_runs
import Theorems.Thm_Printed_length_unary
import Theorems.Thm_Printed_levelMachine_close
import Theorems.Thm_Printed_stCliqueValue
import Theorems.Thm_QueryMachines_stClose
import Theorems.Thm_Value_stCliqueValue


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
namespace Given
theorem _root_.solution {K g C₁ : ℕ} {e : ℝ} {M : CliqueMachine} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e)
    (hNM : ComputesNetworks (groupingMachine K g M) C₁ g K e) : ∃ Cc' : ℕ, AchievedBy (levelMachine K g M) Cc' (g * g) ((rho + 2 / K) * e + 2 / K) := by
  obtain ⟨Cc', h⟩ := level_runs hK hg h0 hNM
  refine ⟨Cc', fun lam B W hl hB hW => ?_⟩
  obtain ⟨T, hT1, hT2⟩ := h (unary lam, unary B) lam B W (length_unary lam) (length_unary B) hl hW
  refine ⟨T, (stClose _ _ _ _ _ _ _ _ _ _).1 ?_, hT2⟩
  rw [levelMachine_close, stCliqueValue (g * g) lam W (by nlinarith) hl]
  exact hT1
end Given
