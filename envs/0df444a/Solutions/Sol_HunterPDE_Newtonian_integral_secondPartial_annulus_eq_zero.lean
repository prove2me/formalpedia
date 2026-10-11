-- Prove2me | solution 1 for HunterPDE.Newtonian.integral_secondPartial_annulus_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:00:23.350416+00:00
-- url     : https://prove2.me/submissions/7b8899c3-767a-4e7d-9dd8-b57b38ed1fce

import Theorems.Thm_MeasureTheory_mixed_green_identity_annulus
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_sphere_flux

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff

theorem solution (n : ℕ) (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R) (i j : Fin n) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      secondPartial (fundamentalSolution n) i j (x - y)) = 0 := by
  have h := MeasureTheory.mixed_green_identity_annulus n (by omega)
    (fundamentalSolution n) (fundamentalSolution_partial n hn).1
    (fun _ => (1 : ℝ)) contDiff_const x R r hR hr hrR i j
  have hp : partialDeriv (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) j =
      (fun _ => 0) := by
    funext y
    simp [partialDeriv, fderiv_const_apply]
  have hpp : secondPartial (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) i j =
      (fun _ => 0) := by
    unfold secondPartial
    rw [hp]
    funext y
    simp [partialDeriv, fderiv_const_apply]
  simp only [hpp, hp, mul_zero, zero_mul, zero_add, mul_one, integral_zero] at h
  rw [fundamentalSolution_sphere_flux n hn R hR i j,
    fundamentalSolution_sphere_flux n hn r hr i j] at h
  simpa using h
