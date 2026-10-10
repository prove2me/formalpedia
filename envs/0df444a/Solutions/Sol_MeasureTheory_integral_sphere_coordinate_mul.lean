-- Prove2me | solution 1 for MeasureTheory.integral_sphere_coordinate_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T23:00:38.102321+00:00
-- url     : https://prove2.me/submissions/79cfc290-9120-4f44-a7ae-325c65e66dfc

import Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory

theorem solution (n : ℕ) (hn : 0 < n) (i j : Fin n) :
    (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ω.1 i * ω.1 j ∂volume.toSphere) =
      HunterPDE.Newtonian.unitBallVolume n * (if i = j then 1 else 0) := by
  classical
  have h := integral_directional_derivative_ball hn (x := 0) (r := 1)
    (f := EuclideanSpace.proj (𝕜 := ℝ) i) zero_lt_one
    (fun y _ => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt)
    (EuclideanSpace.single j 1)
  have hd (y : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) i) y = EuclideanSpace.proj (𝕜 := ℝ) i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).fderiv
  simp_rw [hd] at h
  simpa [ContinuousLinearMap.fderiv, EuclideanSpace.inner_single_left, PiLp.single_apply,
    HunterPDE.Newtonian.unitBallVolume, MeasureTheory.integral_const,
    Measure.real, eq_comm] using h.symm
