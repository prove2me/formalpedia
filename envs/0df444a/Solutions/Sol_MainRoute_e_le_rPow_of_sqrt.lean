-- Prove2me | solution 1 for MainRoute.e_le_rPow_of_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:33.916682+00:00
-- url     : https://prove2.me/submissions/c2297f65-6f24-4c1e-af67-47a777437074

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_MainRoute_EveryMachine
import Definitions.Def_GeneralPieces_Top_EndM
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MainRoute_GeneralInM
import Theorems.Thm_ClauseBound_Alg_End_one_le_log
import Theorems.Thm_ClauseBound_Alg_TopArith_root9_spec
import Theorems.Thm_ClauseBound_Gen_End_one_le_log
import Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_Paper_one_le_lg
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
namespace MainRoute
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {a : ℕ} (ha : ∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) (m : ℕ) :
    e (Q.pick (root9 m)).1.length ≤ ((a * (9 * C₀ + 1) + 1 : ℕ) : ℝ) * SatM.rPow (1 / 2) m := by
  obtain ⟨l, hl⟩ : ∃ l, l = (Q.pick (root9 m)).1.length := ⟨_, rfl⟩
  rw [← hl]
  have hK2 := Q.K_two l
  have h1 : (root9 m).length < S.K (Q.idx (l + 1)) := hl ▸ Q.pick_max (root9 m)
  have h2 : m < S.K (Q.idx l) ^ (9 * C₀) := by
    calc m < ((root9 m).length + 1) ^ 9 := (TopArith.root9_spec m).2
      _ ≤ S.K (Q.idx (l + 1)) ^ 9 := Nat.pow_le_pow_left h1 9
      _ ≤ (S.K (Q.idx l) ^ C₀) ^ 9 := Nat.pow_le_pow_left (Q.K_le l) 9
      _ = _ := by rw [← pow_mul, mul_comm]
  have h3 : m + 2 ≤ S.K (Q.idx l) ^ (9 * C₀ + 1) := by
    rw [pow_succ]
    have : 1 ≤ S.K (Q.idx l) ^ (9 * C₀) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  obtain ⟨y, hy⟩ : ∃ y, y = Real.logb 2 ((m : ℝ) + 2) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = lg (S.K (Q.idx l)) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := hy ▸ ClauseBound.Alg.End.one_le_log m
  have hz1 : 1 ≤ z := hz ▸ VariableBound.Paper.one_le_lg hK2
  have h4 : y ≤ ((9 * C₀ + 1 : ℕ) : ℝ) * z := by
    have g1 : ((m : ℝ) + 2) ≤ (S.K (Q.idx l) : ℝ) ^ (9 * C₀ + 1) := by exact_mod_cast h3
    have g2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) g1
    rw [Real.logb_pow] at g2
    rw [hy, hz]
    exact g2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((9 * C₀ + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hc] at h4
  have hc1 : 1 ≤ c := by rw [hc]; exact_mod_cast (by omega : 1 ≤ 9 * C₀ + 1)
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 (by linarith)
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.2 (by linarith)
  -- √y ≤ c·√z
  have h5 : Real.sqrt y ≤ c * Real.sqrt z := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith
  have h6 : 1 / Real.sqrt z ≤ c / Real.sqrt y := by
    rw [div_le_div_iff₀ hsz hsy]
    linarith
  have hr : SatM.rPow (1 / 2) m = 1 / Real.sqrt y := by
    unfold SatM.rPow
    rw [← hy, ← Real.sqrt_eq_rpow]
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  calc e l ≤ a / Real.sqrt z := hz ▸ ha l
    _ = a * (1 / Real.sqrt z) := by ring
    _ ≤ a * (c / Real.sqrt y) := mul_le_mul_of_nonneg_left h6 ha0
    _ ≤ (a * c + 1) * (1 / Real.sqrt y) := by
        have : 0 ≤ 1 / Real.sqrt y := by positivity
        have e1 : (a : ℝ) * (c / Real.sqrt y) = a * c * (1 / Real.sqrt y) := by ring
        rw [e1]
        nlinarith
    _ = _ := by rw [hr, hc]; push_cast; ring
end MainRoute
