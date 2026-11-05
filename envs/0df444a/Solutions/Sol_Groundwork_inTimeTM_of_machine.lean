-- Prove2me | solution 1 for Groundwork.inTimeTM_of_machine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:18.222207+00:00
-- url     : https://prove2.me/submissions/a20c1a92-df2f-49fb-9bf4-0f2883fbbf0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_StepMachines_Prog_Decode
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_ToTuring_Machine_EndTM
import Theorems.Thm_Groundwork_exists_pow_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_exists_tm


set_option autoImplicit false
section
open Groundwork
open Sat3 Turing
open scoped NNReal
namespace Groundwork
theorem _root_.solution {δ : ℝ≥0} (hδ : 0 < δ) (M : Stepped (List Bool) Bool) [IsPolyT M] (c : ℕ)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      ∃ (T : ℕ) (b : Bool), M.Runs (enc φ) T (c * ((enc φ).length + 1) ^ c) b ∧
        (b = true ↔ Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ ((δ : ℝ) / 2 * n)) : InTimeTM δ := by
  have hδ2 : (0 : ℝ) < (δ : ℝ) / 2 := by have : (0 : ℝ) < δ := hδ; positivity
  obtain ⟨N', c', hfin, hP⟩ := exists_tm M (2 * c)
  obtain ⟨C₁, hC₁⟩ := exists_pow_le (4 * c') hδ2
  refine ⟨N', c' * (c + 1) * 25 ^ c' * C₁, hfin, fun n φ h3 => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n φ h3
  obtain ⟨N, hN⟩ : ∃ N, N = (enc φ).length := ⟨_, rfl⟩
  rw [← hN] at hr
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((δ : ℝ) / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
  have hS : c * (N + 1) ^ c ≤ (N + 2) ^ (2 * c) := by
    have h1 : c ≤ (N + 2) ^ c := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) c)
    have h2 : (N + 1) ^ c ≤ (N + 2) ^ c := Nat.pow_le_pow_left (by omega) c
    calc c * (N + 1) ^ c ≤ (N + 2) ^ c * (N + 2) ^ c := Nat.mul_le_mul h1 h2
      _ = (N + 2) ^ (2 * c) := by rw [two_mul, pow_add]
  obtain ⟨ev⟩ := hP (enc φ) T _ b hr (hN ▸ hS)
  rw [← hN] at ev
  have hle : c' * (T + 1) * (N + 1) ^ c' ≤ ⌊((c' * (c + 1) * 25 ^ c' * C₁ : ℕ) : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * (2 : ℝ) ^ ((δ : ℝ) / 2 * n) := by nlinarith
    have h2 : ((N : ℝ) + 1) ^ c' ≤ (25 : ℝ) ^ c' * (C₁ * (2 : ℝ) ^ ((δ : ℝ) / 2 * n)) := by
      have h5 : N + 1 ≤ 25 * (n + 2) ^ 4 := hN ▸ Groundwork.Decode.length_enc_succ_le h3
      have h6 : ((N : ℝ) + 1) ≤ 25 * ((n : ℝ) + 2) ^ 4 := by exact_mod_cast h5
      calc ((N : ℝ) + 1) ^ c' ≤ (25 * ((n : ℝ) + 2) ^ 4) ^ c' := by gcongr
        _ = (25 : ℝ) ^ c' * ((n : ℝ) + 2) ^ (4 * c') := by rw [mul_pow, ← pow_mul]
        _ ≤ _ := by gcongr; exact hC₁ n
    have h7 : (2 : ℝ) ^ ((δ : ℝ) * n) = (2 : ℝ) ^ ((δ : ℝ) / 2 * n) * (2 : ℝ) ^ ((δ : ℝ) / 2 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    push_cast
    rw [h7]
    calc (c' : ℝ) * ((T : ℝ) + 1) * ((N : ℝ) + 1) ^ c'
        ≤ (c' : ℝ) * (((c : ℝ) + 1) * (2 : ℝ) ^ ((δ : ℝ) / 2 * n)) *
            ((25 : ℝ) ^ c' * (C₁ * (2 : ℝ) ^ ((δ : ℝ) / 2 * n))) := by gcongr
      _ = _ := by ring
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩⟩
end Groundwork
