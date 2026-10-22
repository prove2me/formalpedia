-- Prove2me | solution 1 for GeomDL.Cotangent.heron_formula
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:39:52.900908+00:00
-- url     : https://prove2.me/submissions/56e79487-ea12-4f1d-a177-5055b5d5c00f

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry GeomDL.Cotangent

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {ι : Type*} (x : ι → P) (u v q : ι) :
    triArea (x u) (x v) (x q) =
      heron (edgeLength x u v) (edgeLength x v q) (edgeLength x u q) := by
  unfold triArea heron edgeLength
  have hlaw := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (x u) (x q) (x v)
  rw [dist_comm (x v) (x q)] at hlaw
  set a := dist (x u) (x q)
  set b := dist (x q) (x v)
  set c := dist (x u) (x v)
  set θ := ∠ (x u) (x q) (x v)
  rw [dist_comm (x v) (x q)]
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _ _) (angle_le_pi _ _ _)
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hA : 0 ≤ (1 / 2) * a * b * Real.sin θ := by positivity
  have hsq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
  symm
  rw [Real.sqrt_eq_iff_eq_sq _ hA]
  · rw [mul_pow, hsq]
    linear_combination (1/16 * (a^2 + b^2 - c^2 + 2 * a * b * Real.cos θ)) * hlaw
  · rw [show ((c + a + b) / 2) * ((c + a + b) / 2 - c) * ((c + a + b) / 2 - b) *
        ((c + a + b) / 2 - a) = ((1 / 2) * a * b * Real.sin θ) ^ 2 by
      rw [mul_pow, hsq]
      linear_combination (1/16 * (a^2 + b^2 - c^2 + 2 * a * b * Real.cos θ)) * hlaw]
    positivity
