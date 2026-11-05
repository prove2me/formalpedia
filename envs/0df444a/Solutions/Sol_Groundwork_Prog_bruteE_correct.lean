-- Prove2me | solution 1 for Groundwork.Prog.bruteE_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:50:22.059101+00:00
-- url     : https://prove2.me/submissions/3848195a-42a1-4560-b1cc-c63862b18cbc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_BruteE
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_brute_runs_pow
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
theorem _root_.solution (K : ℕ) : (bruteE K).Correct K (1 / 2) := by
  refine ⟨3 * K ^ 2 + 3 * K + 13, fun C _ lam R c B t S Rm hl ht hR => ?_⟩
  have h := brute_runs_pow (K := K) (lam := lam) (dflt := nilC) (R := R) (c := c) Rm t S B
    (fun v θ h1 h2 => ⟨(hR v θ h1 h2).1, by
      have := (hR v θ h1 h2).2
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this⟩)
  set m := K * (K - 1) / 2 with hm
  have hm2 : 2 * m ≤ K ^ 2 := by
    have h1 := Nat.mul_div_le (K * (K - 1)) 2
    have h2 : K * (K - 1) ≤ K ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  refine ⟨_, h.mono le_rfl ?_, ?_⟩
  · have hx : size c + B + lam c ≤ (size c + B + lam c) ^ (3 * K ^ 2 + 3 * K + 13) :=
      Nat.le_self_pow (by omega) _
    have hK : size K ≤ K + 1 := by
      have := Nat.size_le.2 (Nat.lt_two_pow_self (n := K))
      simp only [size_nat]; omega
    have h1 : m * lam c ≤ K ^ 2 * lam c := Nat.mul_le_mul_right _ (by omega)
    have h2 : K ≤ K * lam c := Nat.le_mul_of_pos_right _ hl
    have h3 := Nat.mul_le_mul_left (3 * K ^ 2 + 3 * K + 13) hx
    have h4 : 2 * size c + 3 * (m * lam c) + 2 * (B * K) + size K + 10
        ≤ (3 * K ^ 2 + 3 * K + 13) * (size c + B + lam c) := by nlinarith
    omega
  · have hexp : ((m * lam c : ℕ) : ℝ) ≤ 1 / 2 * (K : ℝ) ^ 2 * lam c := by
      have : (2 : ℝ) * m ≤ (K : ℝ) ^ 2 := by exact_mod_cast hm2
      push_cast
      have hl0 : (0 : ℝ) ≤ lam c := Nat.cast_nonneg _
      nlinarith
    have hpow : (2 : ℝ) ^ (m * lam c) ≤ (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hlin : (K : ℝ) * (t + 1) + 1 ≤ (3 * (K : ℝ) ^ 2 + 3 * K + 13) * t := by nlinarith [sq_nonneg (K : ℝ)]
    have hQ : (1 : ℝ) ≤ ((B : ℝ) + lam c) ^ (3 * K ^ 2 + 3 * K + 13) := by
      refine one_le_pow₀ ?_
      have : (1 : ℝ) ≤ lam c := by exact_mod_cast hl
      have : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      linarith
    have hP0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) := by positivity
    push_cast
    calc (2 : ℝ) ^ (m * lam c) * ((K : ℝ) * (t + 1) + 1)
        ≤ (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) * ((3 * (K : ℝ) ^ 2 + 3 * K + 13) * t) :=
          mul_le_mul hpow hlin (by positivity) hP0
      _ = (3 * (K : ℝ) ^ 2 + 3 * K + 13) * (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) * 1 * t := by ring
      _ ≤ (3 * (K : ℝ) ^ 2 + 3 * K + 13) * (2 : ℝ) ^ (1 / 2 * (K : ℝ) ^ 2 * lam c) *
            ((B : ℝ) + lam c) ^ (3 * K ^ 2 + 3 * K + 13) * t := by gcongr
end Groundwork.Prog
