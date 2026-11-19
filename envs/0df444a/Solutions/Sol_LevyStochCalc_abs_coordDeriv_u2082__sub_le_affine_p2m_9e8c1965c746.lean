-- Prove2me | solution 1 for LevyStochCalc.abs_coordDeriv_u2082__sub_le_affine_p2m_9e8c1965c746
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:59:29.943915+00:00
-- url     : https://prove2.me/submissions/faec1855-cc76-4b50-819c-2481140bac3e

import Definitions.Def_LevyStochCalc_Brownian_CoordDerivative_F000

open ContinuousLinearMap
open LevyStochCalc

theorem solution {n : ℕ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    {A K : ℝ} (h : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (p q : Fin n) (x y : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y| ≤ A + K * ‖x - y‖ := by
  have hnormp : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hnormq : ‖(Pi.single q 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  calc |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y|
      = ‖(f'' x - f'' y) (Pi.single p 1) (Pi.single q 1)‖ := by
        simp [coordDeriv₂, ContinuousLinearMap.sub_apply, Real.norm_eq_abs]
    _ ≤ ‖f'' x - f'' y‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ * ‖(Pi.single q 1 : Fin n → ℝ)‖ :=
        (f'' x - f'' y).le_opNorm₂ _ _
    _ = ‖f'' x - f'' y‖ := by rw [hnormp, hnormq, mul_one, mul_one]
    _ ≤ A + K * ‖x - y‖ := h x y
