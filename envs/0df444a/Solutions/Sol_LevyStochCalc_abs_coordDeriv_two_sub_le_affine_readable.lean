-- Prove2me | solution 1 for LevyStochCalc.abs_coordDeriv_two_sub_le_affine_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:02.833+00:00
-- url     : https://prove2.me/submissions/fd35ea60-3a72-4985-bc66-98caa840bce8

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- A second partial derivative inherits an affine oscillation bound on the second derivative. -/
theorem solution {A K : ℝ} (h : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (p q : Fin n) (x y : Fin n → ℝ) :
    |LevyStochCalc.coordDeriv₂ f'' p q x - LevyStochCalc.coordDeriv₂ f'' p q y| ≤ A + K * ‖x - y‖ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hnormq : ‖(Pi.single q 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hsub : LevyStochCalc.coordDeriv₂ f'' p q x - LevyStochCalc.coordDeriv₂ f'' p q y
      = (f'' x - f'' y) (Pi.single p 1) (Pi.single q 1) := by simp [LevyStochCalc.coordDeriv₂]
  calc |LevyStochCalc.coordDeriv₂ f'' p q x - LevyStochCalc.coordDeriv₂ f'' p q y|
      = ‖(f'' x - f'' y) (Pi.single p 1) (Pi.single q 1)‖ := by
        rw [hsub]; exact (Real.norm_eq_abs _).symm
    _ ≤ ‖f'' x - f'' y‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ * ‖(Pi.single q 1 : Fin n → ℝ)‖ :=
        (f'' x - f'' y).le_opNorm₂ _ _
    _ = ‖f'' x - f'' y‖ := by rw [hnorm, hnormq, mul_one, mul_one]
    _ ≤ A + K * ‖x - y‖ := h x y
