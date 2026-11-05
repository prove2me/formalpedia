-- Prove2me | solution 1 for GraphProblems.tm_of_stepped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:04:50.002786+00:00
-- url     : https://prove2.me/submissions/a4fff0f7-4dd6-4857-9d45-51b0cc483686

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_CountKSat_Host
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_GraphProblems_Host
import Theorems.Thm_CountKSat_stHostW
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_exists_pow_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
open GraphProblems
open Groundwork CountKSat Turing
namespace GraphProblems
theorem _root_.solution (M : Stepped (List Bool) (List Bool)) [IsPolyT M] {ι : Type} (code out : ι → List Bool) (sz : ι → ℕ)
    {δ : ℝ} (hδ : 0 < δ) (c a d : ℕ) (hlen : ∀ x, (code x).length + 1 ≤ a * (sz x + 2) ^ d)
    (h : ∀ x, ∃ T : ℕ, M.Runs (code x) T (c * (sz x + 2) ^ c) (out x) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * sz x)) :
    ∃ (N : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ ∀ x,
      Nonempty (TM2OutputsInTime N.tm ((code x).map N.inputAlphabet.invFun) (some ((out x).map N.outputAlphabet.invFun))
        ⌊(C : ℝ) * (2 : ℝ) ^ (δ * sz x)⌋₊) := by
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨N', q, hfin, hP⟩ := stHostW M
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((d + c) * q) hδ2
  refine ⟨N', q * (c + 1) * (a + c) ^ q * C₁, hfin, fun x => ?_⟩
  obtain ⟨T, hr, hT⟩ := h x
  obtain ⟨n, hn⟩ : ∃ n, n = sz x := ⟨_, rfl⟩
  rw [← hn] at hr hT ⊢
  have hl := hlen x
  rw [← hn] at hl
  obtain ⟨ev⟩ := hP (code x) T _ _ hr
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
  have hS : (code x).length + c * (n + 2) ^ c + 1 ≤ (a + c) * (n + 2) ^ (d + c) := by
    have h1 : (n + 2) ^ d ≤ (n + 2) ^ (d + c) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (n + 2) ^ c ≤ (n + 2) ^ (d + c) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 := Nat.mul_le_mul_left a h1
    have h4 := Nat.mul_le_mul_left c h2
    rw [add_mul]
    omega
  have hle : q * (T + 1) * ((code x).length + c * (n + 2) ^ c + 1) ^ q ≤
      ⌊((q * (c + 1) * (a + c) ^ q * C₁ : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * (2 : ℝ) ^ (δ / 2 * n) := by nlinarith
    have h2 : ((((code x).length + c * (n + 2) ^ c + 1 : ℕ) : ℝ)) ^ q ≤ ((a : ℝ) + c) ^ q * (C₁ * (2 : ℝ) ^ (δ / 2 * n)) := by
      have h6 : (((code x).length + c * (n + 2) ^ c + 1 : ℕ) : ℝ) ≤ ((a : ℝ) + c) * ((n : ℝ) + 2) ^ (d + c) := by exact_mod_cast hS
      calc ((((code x).length + c * (n + 2) ^ c + 1 : ℕ) : ℝ)) ^ q ≤ (((a : ℝ) + c) * ((n : ℝ) + 2) ^ (d + c)) ^ q := by gcongr
        _ = ((a : ℝ) + c) ^ q * ((n : ℝ) + 2) ^ ((d + c) * q) := by rw [mul_pow, ← pow_mul]
        _ ≤ _ := by gcongr; exact hC₁ n
    have h7 : (2 : ℝ) ^ (δ * n) = (2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    rw [h7]
    calc ((q * (T + 1) * ((code x).length + c * (n + 2) ^ c + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * ((T : ℝ) + 1) * ((((code x).length + c * (n + 2) ^ c + 1 : ℕ) : ℝ)) ^ q := by push_cast; ring
      _ ≤ (q : ℝ) * (((c : ℝ) + 1) * (2 : ℝ) ^ (δ / 2 * n)) * (((a : ℝ) + c) ^ q * (C₁ * (2 : ℝ) ^ (δ / 2 * n))) := by gcongr
      _ = _ := by push_cast; ring
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩
end GraphProblems
