-- Prove2me | solution 1 for NumStochOpt.LogConcave.theorem_5_2_1_shifted_logconcave
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:40:31.277422+00:00
-- url     : https://prove2.me/submissions/dfe9b3f3-07c7-4d5a-9299-a5d74ff7a23b

import Mathlib
import Definitions.Def_LogConcaveOn

set_option autoImplicit false

lemma d7fdd6ea_key (u v p a b : ℝ) (hp : 0 < p) (hu : p ≤ u) (hv : p ≤ v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (u - p) ^ a * (v - p) ^ b + p ≤ u ^ a * v ^ b := by
  have hu0 : 0 < u := lt_of_lt_of_le hp hu
  have hv0 : 0 < v := lt_of_lt_of_le hp hv
  have hU : 0 < u ^ a := Real.rpow_pos_of_pos hu0 a
  have hV : 0 < v ^ b := Real.rpow_pos_of_pos hv0 b
  have h1 := Real.geom_mean_le_arith_mean2_weighted ha hb
    (div_nonneg (sub_nonneg.mpr hu) hu0.le) (div_nonneg (sub_nonneg.mpr hv) hv0.le) hab
  have h2 := Real.geom_mean_le_arith_mean2_weighted ha hb
    (div_nonneg hp.le hu0.le) (div_nonneg hp.le hv0.le) hab
  rw [Real.div_rpow (sub_nonneg.mpr hu) hu0.le, Real.div_rpow (sub_nonneg.mpr hv) hv0.le] at h1
  rw [Real.div_rpow hp.le hu0.le, Real.div_rpow hp.le hv0.le] at h2
  have hpp : p ^ a * p ^ b = p := by
    rw [← Real.rpow_add hp, hab, Real.rpow_one]
  have hsum : a * ((u - p) / u) + b * ((v - p) / v) + (a * (p / u) + b * (p / v)) = 1 := by
    have e1 : (u - p) / u + p / u = 1 := by
      rw [← add_div, sub_add_cancel, div_self hu0.ne']
    have e2 : (v - p) / v + p / v = 1 := by
      rw [← add_div, sub_add_cancel, div_self hv0.ne']
    linear_combination a * e1 + b * e2 + hab
  have hX : (u - p) ^ a * (v - p) ^ b / (u ^ a * v ^ b) + p ^ a * p ^ b / (u ^ a * v ^ b) ≤ 1 := by
    have e1 : (u - p) ^ a / u ^ a * ((v - p) ^ b / v ^ b) = (u - p) ^ a * (v - p) ^ b / (u ^ a * v ^ b) := by
      rw [div_mul_div_comm]
    have e2 : p ^ a / u ^ a * (p ^ b / v ^ b) = p ^ a * p ^ b / (u ^ a * v ^ b) := by
      rw [div_mul_div_comm]
    rw [← e1, ← e2]
    linarith
  rw [hpp, ← add_div, div_le_one (mul_pos hU hV)] at hX
  exact hX

theorem solution {n : ℕ}
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hH : Convex ℝ {x | p ≤ h x})
    (hlc : ConvexOptimization.LogConcaveOn {x | p ≤ h x} h) :
    ConvexOptimization.LogConcaveOn {x | p ≤ h x} (fun x => h x - p) := by
  refine ⟨fun x hx => sub_nonneg.mpr hx, ?_⟩
  intro x hx y hy a b ha hb hab
  have hlc' := hlc.2 x hx y hy a b ha hb hab
  change p ≤ h x at hx
  change p ≤ h y at hy
  have k := d7fdd6ea_key (h x) (h y) p a b hp0 hx hy ha hb hab
  show (h x - p) ^ a * (h y - p) ^ b ≤ h (a • x + b • y) - p
  linarith
