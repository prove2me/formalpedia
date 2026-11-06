-- Prove2me | solution 4 for Komlos.banaszczyk_bound
-- status  : ACCEPTED   (prove)
-- author  : @刘柄含
-- created : 2026-11-06T05:45:08.277827+00:00
-- url     : https://prove2.me/submissions/e97d532f-52c7-4b47-b0c0-05ac11f48666

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Komlos_model
import Theorems.Thm_Komlos_bansal_jiang_komlos_bound

/-!
Banaszczyk's Komlós bound follows from the stronger Bansal–Jiang bound.
The logarithmic comparison below is uniform for all family sizes.
-/

set_option autoImplicit false

open Komlos
open scoped BigOperators

private theorem absorb_log_log (γ : ℝ) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      Real.log (n + 2) ^ ((1 : ℝ) / 4) * Real.log (Real.log (n + 8)) ^ γ
        ≤ K * Real.sqrt (Real.log (n + 2)) := by
  let δ : ℝ := 1 / (4 * γ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδγ : δ * γ = 1 / 4 := by
    dsimp [δ]
    field_simp [hγ.ne']
  let K : ℝ := 3 ^ ((1 : ℝ) / 4) / δ ^ γ
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  let L : ℝ := Real.log ((n : ℝ) + 2)
  have hL : 0 < L := Real.log_pos (by linarith)
  have hshift : (n : ℝ) + 8 ≤ ((n : ℝ) + 2) ^ 3 := by
    calc
      (n : ℝ) + 8 ≤ 4 * ((n : ℝ) + 2) := by linarith
      _ ≤ ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 2) := by
        gcongr
        nlinarith [sq_nonneg (n : ℝ)]
      _ = ((n : ℝ) + 2) ^ 3 := by ring
  have hlog : Real.log ((n : ℝ) + 8) ≤ 3 * L := by
    simpa [L, Real.log_pow] using Real.log_le_log (by positivity) hshift
  have hlog_pos : 0 < Real.log ((n : ℝ) + 8) := Real.log_pos (by linarith)
  have hloglog_nonneg : 0 ≤ Real.log (Real.log ((n : ℝ) + 8)) := by
    apply Real.log_nonneg
    rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hgrowth :
      Real.log (Real.log ((n : ℝ) + 8)) ≤ (3 * L) ^ δ / δ :=
    (Real.log_le_log hlog_pos hlog).trans (Real.log_le_rpow_div (by positivity) hδ)
  change L ^ ((1 : ℝ) / 4) * Real.log (Real.log ((n : ℝ) + 8)) ^ γ ≤
    K * Real.sqrt L
  calc
    _ ≤ L ^ ((1 : ℝ) / 4) * (((3 * L) ^ δ / δ) ^ γ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hloglog_nonneg hgrowth hγ.le)
        (by positivity)
    _ = K * Real.sqrt L := by
      rw [Real.div_rpow (by positivity) hδ.le, ← Real.rpow_mul (by positivity),
        hδγ, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hL.le, Real.sqrt_eq_rpow]
      dsimp [K]
      rw [show (1 : ℝ) / 2 = 1 / 4 + 1 / 4 by norm_num, Real.rpow_add hL]
      ring

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (n + 2)) := by
  obtain ⟨C, γ, hC, hγ, hsign⟩ := Komlos.bansal_jiang_komlos_bound
  obtain ⟨K, hK, hbound⟩ := absorb_log_log γ hγ
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro n m v hv
  obtain ⟨ε, hε, hε_bound⟩ := hsign n m v hv
  refine ⟨ε, hε, fun j => (hε_bound j).trans ?_⟩
  simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left (hbound n) hC.le
