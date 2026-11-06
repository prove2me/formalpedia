-- Prove2me | solution 1 for Given.onFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:10:10.184048+00:00
-- url     : https://prove2.me/submissions/a0ebfbbc-a355-410b-aabc-e0e2f4c3fe62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Eight_ViaGrouping_satNet_isNetworkP
import Theorems.Thm_Given_onSteps
import Theorems.Thm_Given_stFormulaGiven
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_size_under
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
theorem _root_.solution {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hg : 0 < g) (k : ℕ) (h : ComputesNetworks NM C₁ g K e) :
    (NM.PolyTimeSteps → Nonempty (IsPolyT (networkOnSteps g NM (formulaProcs g k)))) ∧ ∃ C : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      (networkOnSteps g NM (formulaProcs g k)).Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * k) + 10 + C * (size Φ + satPf g k Φ + 1) ^ C) (wordNet g k Φ).value ∧
      (T : ℝ) ≤ C * (2 : ℝ) ^ (e * ((wordNet g k Φ).U : ℝ) + (e + 2) * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C := by
  refine ⟨(onSteps h (stFormulaGiven g hg k [])).1, 3 * C₁ + 5, fun Φ => ?_⟩
  obtain ⟨_, hv, hU⟩ := satNet_isNetworkP hg k Φ
  obtain ⟨T, hrun, hT⟩ := (onSteps h (stFormulaGiven g hg k Φ)).2
  rw [hv] at hrun
  rw [hU, Nat.cast_one, mul_one] at hT
  refine ⟨T, hrun.mono le_rfl ?_, hT.trans ?_⟩
  · have := size_under (size Φ) (satPf g k Φ) C₁
    omega
  · have he : e * ((wordNet g k Φ).U : ℝ) + (e + 2) * ((g : ℝ) * (satPf g k Φ : ℝ)) / K = e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K := by ring
    rw [he]
    have hY : (1 : ℝ) ≤ (satPf g k Φ : ℝ) + 1 := by linarith [(Nat.cast_nonneg (satPf g k Φ) : (0 : ℝ) ≤ _)]
    have h2 : ((satPf g k Φ : ℝ) + 1) ^ C₁ ≤ ((satPf g k Φ : ℝ) + 1) ^ (3 * C₁ + 5) := pow_le_pow_right₀ hY (by omega)
    have h3 : 3 * (C₁ : ℝ) ≤ ((3 * C₁ + 5 : ℕ) : ℝ) := by push_cast; linarith
    calc 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁)
        = 3 * (C₁ : ℝ) * (2 : ℝ) ^ (e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right h3 (by positivity)) h2 (by positivity) (by positivity)
end Given
