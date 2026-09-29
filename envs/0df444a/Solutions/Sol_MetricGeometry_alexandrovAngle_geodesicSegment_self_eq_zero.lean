-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_geodesicSegment_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T02:03:44.239528+00:00
-- url     : https://prove2.me/submissions/a61ba86a-bf57-472d-bfe0-f421e4c3cfa1

import Definitions.Def_metric_alexandrov_angle

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X] (p y : X) (g : ℝ → X)
    (hg : IsGeodesicSegment g p y) (hy : dist p y ≠ 0) :
    alexandrovAngle p g g = 0 := by
  have hD : 0 < dist p y := lt_of_le_of_ne dist_nonneg (Ne.symm hy)
  have key : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ t ∈ Set.Ioo (0:ℝ) 1,
      comparisonAngle p (g s) (g t) = 0 := by
    intro s hs t ht
    have hsI : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have e0 : dist p (g s) = s * dist p y := by
      have := hg.2.2 0 ⟨le_refl 0, zero_le_one⟩ s hsI
      rw [hg.1] at this
      rw [this, abs_of_nonpos (by linarith [hs.1]), neg_sub, sub_zero]
    have e1 : dist p (g t) = t * dist p y := by
      have := hg.2.2 0 ⟨le_refl 0, zero_le_one⟩ t htI
      rw [hg.1] at this
      rw [this, abs_of_nonpos (by linarith [ht.1]), neg_sub, sub_zero]
    have e2 : dist (g s) (g t) = |s - t| * dist p y := hg.2.2 s hsI t htI
    unfold comparisonAngle
    rw [e0, e1, e2]
    have hquot : ((s * dist p y) ^ 2 + (t * dist p y) ^ 2 - (|s - t| * dist p y) ^ 2)
        / (2 * (s * dist p y) * (t * dist p y)) = 1 := by
      have hs0 : s ≠ 0 := ne_of_gt hs.1
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      rw [mul_pow, mul_pow, mul_pow, sq_abs]
      field_simp
      ring
    rw [hquot, Real.arccos_one]
  have hcongr : Filter.limsup (fun st : ℝ × ℝ => comparisonAngle p (g st.1) (g st.2))
        ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)))
      = Filter.limsup (fun _ : ℝ × ℝ => (0:ℝ)) ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) := by
    refine Filter.limsup_congr ?_
    rw [Filter.eventually_prod_iff]
    exact ⟨fun a => a ∈ Set.Ioo (0:ℝ) 1, Ioo_mem_nhdsGT one_pos,
      fun b => b ∈ Set.Ioo (0:ℝ) 1, Ioo_mem_nhdsGT one_pos,
      fun {a} ha {b} hb => key a ha b hb⟩
  show Filter.limsup (fun st : ℝ × ℝ => comparisonAngle p (g st.1) (g st.2))
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) = 0
  rw [hcongr, Filter.limsup_const]
