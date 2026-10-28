-- Prove2me | solution 1 for GeomDL.Sets.eq_7_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:36:35.514541+00:00
-- url     : https://prove2.me/submissions/39d1b017-d51f-4058-98be-646c3dca9f27

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

open GeomDL.Sets

theorem solution {n d d' : ℕ} (Θ : Matrix (Fin d) (Fin d') ℝ) :
    IsPermEquivariant (nodeLinear Θ : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin d') ℝ) ∧
      ∀ (X : Matrix (Fin n) (Fin d) ℝ) (u : Fin n), nodeLinear Θ X u = (Matrix.transpose Θ).mulVec (X u) := by
  refine ⟨fun σ X => ?_, fun X u => ?_⟩
  · ext i j
    simp [nodeLinear, permRows, Matrix.mul_apply]
  · funext j
    simp [nodeLinear, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
