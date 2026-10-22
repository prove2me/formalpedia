-- Prove2me | solution 1 for GeomDL.Cotangent.cot_angle_eq_lengths
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:46:22.807142+00:00
-- url     : https://prove2.me/submissions/94650c7c-1071-474e-a50f-969cffea9f6b

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry GeomDL.Cotangent

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {ι : Type*} (x : ι → P) {u v q : ι}
    (hnd : AffineIndependent ℝ ![x u, x v, x q]) :
    Real.cot (∠ (x u) (x q) (x v)) =
      (-(edgeLength x u v) ^ 2 + (edgeLength x v q) ^ 2 + (edgeLength x u q) ^ 2) /
        (4 * triArea (x u) (x v) (x q)) := by
  have hinj := hnd.injective
  have huq : x u ≠ x q := fun h => by
    have := @hinj 0 2 (by simpa using h); exact absurd this (by decide)
  have hvq : x v ≠ x q := fun h => by
    have := @hinj 1 2 (by simpa using h); exact absurd this (by decide)
  unfold triArea edgeLength
  have hlaw := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (x u) (x q) (x v)
  rw [dist_comm (x v) (x q)]
  have ha : dist (x u) (x q) ≠ 0 := dist_ne_zero.2 huq
  have hb : dist (x q) (x v) ≠ 0 := dist_ne_zero.2 (Ne.symm hvq)
  rw [Real.cot_eq_cos_div_sin]
  have hnum : -dist (x u) (x v) ^ 2 + dist (x q) (x v) ^ 2 + dist (x u) (x q) ^ 2 =
      (2 * dist (x u) (x q) * dist (x q) (x v)) * Real.cos (∠ (x u) (x q) (x v)) := by
    rw [dist_comm (x v) (x q)] at hlaw; nlinarith [hlaw]
  have hden : 4 * (1 / 2 * dist (x u) (x q) * dist (x q) (x v) * Real.sin (∠ (x u) (x q) (x v))) =
      (2 * dist (x u) (x q) * dist (x q) (x v)) * Real.sin (∠ (x u) (x q) (x v)) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (by positivity)]
