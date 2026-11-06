-- Prove2me | solution 1 for Given.stCountCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:47.156197+00:00
-- url     : https://prove2.me/submissions/a1a450d1-6909-4893-9d41-68e76e203972

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_stClique
import Theorems.Thm_Given_onFormula
import Theorems.Thm_Eight_ViaGrouping_Correct_onFormula
import Theorems.Thm_Exits_stClique
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Paper_levelK_ge
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_cost_of_bound
import Theorems.Thm_Printed_cost_with_first_line
import Theorems.Thm_Printed_firstLine_poly
import Theorems.Thm_Printed_onFormula
import Theorems.Thm_Printed_stClique
import Theorems.Thm_Printed_stGroupingPoly
import Theorems.Thm_Printed_stGroupingTied
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : StCountCost := by
  intro δ' ℓ hδ' h1 hK hE
  obtain ⟨hp, Cc, hA⟩ := stClique ℓ
  have hK2 : 2 ≤ levelK ℓ := (by norm_num : 2 ≤ 64).trans (levelK_ge ℓ)
  obtain ⟨C₁, hC₁⟩ := stGroupingTied (levelK ℓ) (δ' / 12) (CLIQUE ℓ) Cc hK2 (by positivity) (hA.mono hE)
  have hC₁' : ComputesNetworks (NETWORK ℓ) C₁ (levelG ℓ) (levelK ℓ) (δ' / 12) := hC₁
  have hg : 0 < levelG ℓ := Nat.mul_pos (by norm_num) (pow_pos (by omega) 8)
  obtain ⟨hpoly, hbound⟩ := onFormula hg 3 hC₁'
  obtain ⟨A, hA'⟩ := cost_of_bound hδ' h1 hg hK hbound
  exact ⟨firstLine_poly (hpoly (stGroupingPoly _ _ _ hp)), A + 4, cost_with_first_line hA'⟩
end Given
