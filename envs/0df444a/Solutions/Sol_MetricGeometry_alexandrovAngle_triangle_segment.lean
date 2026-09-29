-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_triangle_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T02:06:40.197382+00:00
-- url     : https://prove2.me/submissions/7d38b7c2-9211-4820-850f-965b1b0a8c95

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_alexandrovAngle_triangle
import Theorems.Thm_MetricGeometry_alexandrovAngle_reparam

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p y y' y'' : X)
    (g g' g'' : ℝ → X)
    (hg : IsGeodesicSegment g p y) (hg' : IsGeodesicSegment g' p y')
    (hg'' : IsGeodesicSegment g'' p y'')
    (hy : dist p y ≠ 0) (hy' : dist p y' ≠ 0) (hy'' : dist p y'' ≠ 0) :
    alexandrovAngle p g' g'' ≤ alexandrovAngle p g g' + alexandrovAngle p g g'' := by
  have hD : 0 < dist p y := lt_of_le_of_ne dist_nonneg (Ne.symm hy)
  have hD' : 0 < dist p y' := lt_of_le_of_ne dist_nonneg (Ne.symm hy')
  have hD'' : 0 < dist p y'' := lt_of_le_of_ne dist_nonneg (Ne.symm hy'')
  have harc : ∀ (q : X) (h : ℝ → X), IsGeodesicSegment h p q → 0 < dist p q →
      ∀ t ∈ Set.Ioc (0:ℝ) (dist p q), dist p (h ((dist p q)⁻¹ * t)) = t := by
    intro q h hh hq t ht
    have hmem : (dist p q)⁻¹ * t ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact mul_nonneg (inv_nonneg.mpr dist_nonneg) ht.1.le
      · rw [inv_mul_le_one₀ hq]; exact ht.2
    have := hh.2.2 0 ⟨le_refl 0, zero_le_one⟩ ((dist p q)⁻¹ * t) hmem
    rw [hh.1] at this
    rw [this, abs_of_nonpos (by
      have h0 : 0 ≤ (dist p q)⁻¹ * t := mul_nonneg (inv_nonneg.mpr dist_nonneg) ht.1.le
      linarith), neg_sub, sub_zero]
    field_simp
  set a := min (min (dist p y) (dist p y')) (dist p y'') with hadef
  have ha : 0 < a := lt_min (lt_min hD hD') hD''
  have hsub : ∀ (q : X) (h : ℝ → X), IsGeodesicSegment h p q → 0 < dist p q →
      a ≤ dist p q → ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (h ((dist p q)⁻¹ * t)) = t := by
    intro q h hh hq hle t ht
    exact harc q h hh hq t ⟨ht.1, le_trans ht.2 hle⟩
  have h1 := hsub y g hg hD (le_trans (min_le_left _ _) (min_le_left _ _))
  have h2 := hsub y' g' hg' hD' (le_trans (min_le_left _ _) (min_le_right _ _))
  have h3 := hsub y'' g'' hg'' hD'' (min_le_right _ _)
  have hkey := MetricGeometry.alexandrovAngle_triangle p
    (fun t => g ((dist p y)⁻¹ * t)) (fun t => g' ((dist p y')⁻¹ * t))
    (fun t => g'' ((dist p y'')⁻¹ * t)) a ha h1 h2 h3
  rw [MetricGeometry.alexandrovAngle_reparam p g' g'' _ _ (inv_pos.mpr hD') (inv_pos.mpr hD''),
    MetricGeometry.alexandrovAngle_reparam p g g' _ _ (inv_pos.mpr hD) (inv_pos.mpr hD'),
    MetricGeometry.alexandrovAngle_reparam p g g'' _ _ (inv_pos.mpr hD) (inv_pos.mpr hD'')] at hkey
  exact hkey
