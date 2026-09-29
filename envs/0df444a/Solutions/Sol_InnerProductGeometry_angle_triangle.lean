-- Prove2me | solution 1 for InnerProductGeometry.angle_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T08:01:01.772537+00:00
-- url     : https://prove2.me/submissions/355860df-3ec6-4c12-b675-32e809fb79de

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_alexandrovAngle_ray_eq_angle
import Theorems.Thm_MetricGeometry_alexandrovAngle_triangle

open MetricGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : E) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    InnerProductGeometry.angle x z
      ≤ InnerProductGeometry.angle x y + InnerProductGeometry.angle y z := by
  have hnpos : ∀ w : E, w ≠ 0 → (0 : ℝ) < ‖w‖⁻¹ := by
    intro w hw
    have : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    positivity
  have hunit : ∀ w : E, w ≠ 0 → ‖‖w‖⁻¹ • w‖ = 1 := by
    intro w hw
    have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hnpos w hw), inv_mul_cancel₀ (ne_of_gt hn)]
  have hray : ∀ w : E, w ≠ 0 → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      dist (0 : E) ((0 : E) + t • (‖w‖⁻¹ • w)) = t := by
    intro w hw t ht
    rw [zero_add, dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1,
      hunit w hw, mul_one]
  have h := MetricGeometry.alexandrovAngle_triangle (0 : E)
    (fun t => (0 : E) + t • (‖y‖⁻¹ • y)) (fun t => (0 : E) + t • (‖x‖⁻¹ • x))
    (fun t => (0 : E) + t • (‖z‖⁻¹ • z)) 1 one_pos (hray y hy) (hray x hx) (hray z hz)
  rw [MetricGeometry.alexandrovAngle_ray_eq_angle,
    MetricGeometry.alexandrovAngle_ray_eq_angle,
    MetricGeometry.alexandrovAngle_ray_eq_angle] at h
  have hsc : ∀ a b : E, a ≠ 0 → b ≠ 0 →
      InnerProductGeometry.angle (‖a‖⁻¹ • a) (‖b‖⁻¹ • b)
        = InnerProductGeometry.angle a b := by
    intro a b ha hb
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (hnpos a ha),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (hnpos b hb)]
  rw [hsc x z hx hz, hsc y x hy hx, hsc y z hy hz,
    InnerProductGeometry.angle_comm y x] at h
  exact h
