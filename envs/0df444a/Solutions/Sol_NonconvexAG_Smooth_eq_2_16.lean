-- Prove2me | solution 1 for NonconvexAG.Smooth.eq_2_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:23:13.930212+00:00
-- url     : https://prove2.me/submissions/e87672bb-5024-4fbe-85c6-5a1113f0b886

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Smooth_AGRun

set_option autoImplicit false
open NonconvexAG.Smooth

lemma nas_Gamma_one (α : ℕ → ℝ) : Gamma α 1 = 1 := by
  simp [Gamma]

lemma nas_Gamma_succ (α : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Gamma α (k + 1) = (1 - α (k + 1)) * Gamma α k := by
  unfold Gamma
  rw [Finset.prod_Icc_succ_top (by omega), mul_comm]

lemma nas_Gamma_pos (α : ℕ → ℝ) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) (k : ℕ) :
    0 < Gamma α k := by
  unfold Gamma
  apply Finset.prod_pos
  intro i hi
  have := hα i (Finset.mem_Icc.mp hi).1
  linarith [this.2]

theorem solution (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) :
    ∀ k, 1 ≤ k → ∑ τ ∈ Finset.Icc 1 k, α τ / Gamma α τ = 1 / Gamma α k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp [nas_Gamma_one, hα1]
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, nas_Gamma_succ α k hk]
    have h1 := nas_Gamma_pos α hα k
    have h2 := (hα (k + 1) (by omega)).2
    have h3 : (1 - α (k + 1)) ≠ 0 := by linarith
    field_simp
    ring
