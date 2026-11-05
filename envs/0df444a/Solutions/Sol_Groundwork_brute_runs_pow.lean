-- Prove2me | solution 1 for Groundwork.brute_runs_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:48:27.870455+00:00
-- url     : https://prove2.me/submissions/0fd50dd7-d660-4d3b-b34f-0dede1320b99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Definitions.Def_StepMachines_Prog_Brute
import Theorems.Thm_Groundwork_brute_runs
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
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
open Groundwork
open Finset Stepped
variable {C : Type} [HasSize C]
namespace Groundwork
theorem _root_.solution {K : ℕ} {lam : C → ℕ} {dflt : C → List Bool}
    {R : Stepped (C × ℕ × List (List Bool)) ℤ} {c : C} (Rm : Inst (Fin K) (List Bool)) (t S B : ℕ)
    (hR : ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = lam c) → θ v = dflt c →
      R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ (Rm v θ).natAbs ≤ 2 ^ B) :
    (brute K lam dflt R).Runs c (2 ^ (K * (K - 1) / 2 * lam c) * (K * (t + 1) + 1))
      (2 * size c + 3 * (K * (K - 1) / 2 * lam c) + 2 * (B * K) + size K + S + 10)
      (Inst.ZW (lam c) (dflt c) Rm) := by
  refine (brute_runs Rm t S (2 ^ B) Nat.one_le_two_pow hR).mono le_rfl ?_
  rw [← pow_mul, ← pow_add]
  simp only [size_nat, Nat.size_pow]
  omega
end Groundwork
