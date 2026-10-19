-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.matrix_mulVecLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T13:09:28.830371+00:00
-- url     : https://prove2.me/submissions/dc81e980-9965-45f8-be51-b5e03ab2bca4

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
  ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) rho =
    ∑ c : InterpolationMatrix.Column w0 w H,
      InterpolationMatrix.matrix K w0 v0 theta w H r G rho c * x c := by
  classical
  simp [Matrix.mulVec, dotProduct]
