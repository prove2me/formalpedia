-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineNearZeroIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:36:55.515666+00:00
-- url     : https://prove2.me/submissions/29ed6f68-7466-4048-8b74-a1eb66b9f9d2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! At the origin the stable-index-one cosine kernel is uniformly bounded. -/
theorem solution :
    IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
    (Set.Ioo (0 : ℝ) 1) := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ))
      (Ioo (0 : ℝ) 1) := by
    exact integrableOn_const (by rw [Real.volume_Ioo]; norm_num)
  apply hconst.mono'
  · have hm : Measurable (fun r : ℝ => (1 - Real.cos r) / r ^ 2) := by
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hrpos : 0 < r := hr.1
    have hn : 0 ≤ 1 - Real.cos r := sub_nonneg.mpr (Real.cos_le_one r)
    have hb : 1 - Real.cos r ≤ r ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := r)]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (sq_nonneg r))]
    apply (div_le_iff₀ (pow_pos hrpos 2)).2
    nlinarith [hb]
