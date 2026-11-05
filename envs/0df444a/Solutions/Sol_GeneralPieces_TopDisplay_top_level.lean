-- Prove2me | solution 1 for GeneralPieces.TopDisplay.top_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:59.247481+00:00
-- url     : https://prove2.me/submissions/63b844db-38b4-4314-b7a1-05b09ffadb4a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_m_lt_pow
import Theorems.Thm_GeneralPieces_TopDisplay_K_ge_root90
import Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_display
import Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_main
import Theorems.Thm_ClauseBound_Alg_TopArith_root9_spec
import Theorems.Thm_ClauseBound_Gen_Seq_topK_idx
import Theorems.Thm_GeneralPieces_PartA_e_ge_half_pow
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (Q : (solverOf P).Seq (e ρ x₀) C₀)
    (hQ : ∀ l, Q.idx l = idx P x₀ l) (k m : ℕ) (hk : 1 ≤ k) (hm : K x₀ 0 ^ 9 ≤ m) :
    K x₀ (Q.pick (root9 m)).1.length ^ 9 ≤ m ∧ m < K x₀ ((Q.pick (root9 m)).1.length + 1) ^ 9 ∧
    (m : ℝ) ^ (1 / 90 : ℝ) ≤ K x₀ (Q.pick (root9 m)).1.length ∧
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ 2 * e ρ x₀ (Q.pick (root9 m)).1.length * k * m + (2 * C₀ + 15 : ℕ) *
      ((k : ℝ) * m / K x₀ (Q.pick (root9 m)).1.length +
        (K x₀ (Q.pick (root9 m)).1.length : ℝ) ^ 8 * Real.logb 2 (K x₀ (Q.pick (root9 m)).1.length) +
        (K x₀ (Q.pick (root9 m)).1.length : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) ∧
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ 2 * e ρ x₀ (Q.pick (root9 m)).1.length * k * m +
      (203 * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by
  have hKi : ∀ l, (solverOf P).K (Q.idx l) = K x₀ l := fun l => by rw [hQ]; exact Seq.topK_idx P x₀ l
  obtain ⟨hr1, hr2⟩ := root9_spec m
  have hK0 : (solverOf P).K (Q.idx 0) ≤ (root9 m).length := by
    rw [hKi]
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 9
    exact absurd (h'.trans hm) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root9 m)
  have hidx := Q.pick_idx (root9 m)
  rw [hidx, hKi] at hle
  rw [hKi] at hmax
  rw [hidx]
  generalize (Q.pick (root9 m)).1.length = l at *
  have h1 : K x₀ l ^ 9 ≤ m := (Nat.pow_le_pow_left hle 9).trans hr1
  have h2 : m < K x₀ (l + 1) ^ 9 := lt_of_lt_of_le hr2 (Nat.pow_le_pow_left (Nat.succ_le_of_lt hmax) 9)
  have h3 := m_lt_pow x₀ l m (by omega) h2
  have hρ0 : 0 < ρ := by linarith
  have he0 : 0 ≤ e ρ x₀ l := (by positivity : 0 ≤ 1 / 2 * ρ ^ l).trans (e_ge_half_pow ρ x₀ l hρ)
  have hK2 : 2 ≤ (solverOf P).K (Q.idx l) := Q.K_two l
  have d1 := needTop_le_display (solverOf P) (Q.idx l) (e ρ x₀ l) C₀ k m he0 (Q.e_le l) hK2 hk (by rw [hKi]; exact h1) (Q.rate l)
  have d2 := needTop_le_main (solverOf P) (Q.idx l) (e ρ x₀ l) C₀ k m he0 (Q.e_le l) hK2 hk (by rw [hKi]; exact h1)
    (by rw [hKi]; exact h3.le) (Q.rate l)
  rw [hKi] at d1
  exact ⟨h1, h2, K_ge_root90 x₀ l m (by omega) h2, d1, d2⟩
end GeneralPieces.TopDisplay
