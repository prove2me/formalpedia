-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T01:11:45.96808+00:00
-- url     : https://prove2.me/submissions/37f6a2a5-4d74-4f5e-bfd3-c2618e2639f6

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_mem_Icc
import Theorems.Thm_MetricGeometry_comparisonAngle_le_add_of_forall_comparisonAngle_le

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X] (p : X) (c c' c'' : ℝ → X)
    (a : ℝ) (ha : 0 < a)
    (hc : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c t) = t)
    (hc' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c' t) = t)
    (hc'' : ∀ t ∈ Set.Ioc (0:ℝ) a, dist p (c'' t) = t) :
    alexandrovAngle p c' c'' ≤ alexandrovAngle p c c' + alexandrovAngle p c c'' := by
  set F : Filter (ℝ × ℝ) := (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)) with hF
  have hNeBot : F.NeBot := by rw [hF]; infer_instance
  haveI := hNeBot
  have hbd : ∀ g1 g2 : ℝ → X, IsBoundedUnder (· ≤ ·) F
      (fun st : ℝ × ℝ => comparisonAngle p (g1 st.1) (g2 st.2)) :=
    fun g1 g2 => Filter.isBoundedUnder_of
      ⟨Real.pi, fun st => (MetricGeometry.comparisonAngle_mem_Icc p (g1 st.1) (g2 st.2)).2⟩
  have hbd' : ∀ g1 g2 : ℝ → X, IsBoundedUnder (· ≥ ·) F
      (fun st : ℝ × ℝ => comparisonAngle p (g1 st.1) (g2 st.2)) :=
    fun g1 g2 => Filter.isBoundedUnder_of
      ⟨0, fun st => (MetricGeometry.comparisonAngle_mem_Icc p (g1 st.1) (g2 st.2)).1⟩
  have hcob : ∀ g1 g2 : ℝ → X, IsCoboundedUnder (· ≤ ·) F
      (fun st : ℝ × ℝ => comparisonAngle p (g1 st.1) (g2 st.2)) :=
    fun g1 g2 => (hbd' g1 g2).isCoboundedUnder_le
  have hnn : ∀ g1 g2 : ℝ → X, 0 ≤ alexandrovAngle p g1 g2 := by
    intro g1 g2
    have h0 : Filter.limsup (fun _ : ℝ × ℝ => (0:ℝ)) F = 0 := Filter.limsup_const 0
    have hle : Filter.limsup (fun _ : ℝ × ℝ => (0:ℝ)) F
        ≤ Filter.limsup (fun st : ℝ × ℝ => comparisonAngle p (g1 st.1) (g2 st.2)) F :=
      Filter.limsup_le_limsup
        (Eventually.of_forall fun st =>
          (MetricGeometry.comparisonAngle_mem_Icc p (g1 st.1) (g2 st.2)).1)
        (IsBoundedUnder.isCoboundedUnder_le
          (Filter.isBoundedUnder_of ⟨0, fun _ : ℝ × ℝ => le_refl (0:ℝ)⟩))
        (hbd g1 g2)
    rw [h0] at hle
    exact hle
  -- extraction helper
  have key : ∀ Q : ℝ → ℝ → Prop, (∀ᶠ st in F, Q st.1 st.2) →
      ∃ ε > (0:ℝ), ∀ s ∈ Set.Ioo (0:ℝ) ε, ∀ t ∈ Set.Ioo (0:ℝ) ε, Q s t := by
    intro Q hQ
    rw [hF, Filter.eventually_prod_iff] at hQ
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := hQ
    obtain ⟨u1, hu1, hs1⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpa
    obtain ⟨u2, hu2, hs2⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpb
    refine ⟨min u1 u2, lt_min hu1 hu2, fun s hs t ht => ?_⟩
    exact hab (hs1 ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
      (hs2 ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩)
  have key2 : ∀ (Q : ℝ → ℝ → Prop) (ε : ℝ), 0 < ε →
      (∀ s ∈ Set.Ioo (0:ℝ) ε, ∀ t ∈ Set.Ioo (0:ℝ) ε, Q s t) →
      ∀ᶠ st in F, Q st.1 st.2 := by
    intro Q ε hε h
    rw [hF, Filter.eventually_prod_iff]
    exact ⟨fun s => s ∈ Set.Ioo (0:ℝ) ε, Ioo_mem_nhdsGT hε,
      fun t => t ∈ Set.Ioo (0:ℝ) ε, Ioo_mem_nhdsGT hε,
      fun {s} hs {t} ht => h s hs t ht⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have e1 : ∀ᶠ st in F,
      comparisonAngle p (c st.1) (c' st.2) < alexandrovAngle p c c' + δ / 4 :=
    Filter.eventually_lt_of_limsup_lt (by
      show alexandrovAngle p c c' < alexandrovAngle p c c' + δ / 4
      linarith) (hbd c c')
  have e2 : ∀ᶠ st in F,
      comparisonAngle p (c st.1) (c'' st.2) < alexandrovAngle p c c'' + δ / 4 :=
    Filter.eventually_lt_of_limsup_lt (by
      show alexandrovAngle p c c'' < alexandrovAngle p c c'' + δ / 4
      linarith) (hbd c c'')
  obtain ⟨ε1, hε1, H1⟩ := key
    (fun s t => comparisonAngle p (c s) (c' t) < alexandrovAngle p c c' + δ / 4) e1
  obtain ⟨ε2, hε2, H2⟩ := key
    (fun s t => comparisonAngle p (c s) (c'' t) < alexandrovAngle p c c'' + δ / 4) e2
  set ε := min (min ε1 ε2) a with hεdef
  have hε : 0 < ε := lt_min (lt_min hε1 hε2) ha
  have hεa : ε ≤ a := min_le_right _ _
  have hεe1 : ε ≤ ε1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεe2 : ε ≤ ε2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have main : ∀ s ∈ Set.Ioo (0:ℝ) ε, ∀ t ∈ Set.Ioo (0:ℝ) ε,
      comparisonAngle p (c' s) (c'' t)
        ≤ (alexandrovAngle p c c' + δ / 4) + (alexandrovAngle p c c'' + δ / 4) := by
    intro s hs t ht
    have hds : dist p (c' s) = s :=
      hc' s ⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 hεa)⟩
    have hdt : dist p (c'' t) = t :=
      hc'' t ⟨ht.1, le_of_lt (lt_of_lt_of_le ht.2 hεa)⟩
    refine MetricGeometry.comparisonAngle_le_add_of_forall_comparisonAngle_le p (c' s) (c'' t) c
      _ _ (by linarith [hnn c c']) (by linarith [hnn c c''])
      (by rw [hds]; exact hs.1) (by rw [hdt]; exact ht.1) ?_ ?_ ?_
    · intro r hr
      rw [hds, hdt] at hr
      have hrlt : r < ε := lt_of_le_of_lt hr.2 (max_lt hs.2 ht.2)
      exact hc r ⟨hr.1, le_of_lt (lt_of_lt_of_le hrlt hεa)⟩
    · intro r hr
      rw [hds, hdt] at hr
      have hrlt : r < ε := lt_of_le_of_lt hr.2 (max_lt hs.2 ht.2)
      exact le_of_lt (H1 r ⟨hr.1, lt_of_lt_of_le hrlt hεe1⟩ s
        ⟨hs.1, lt_of_lt_of_le hs.2 hεe1⟩)
    · intro r hr
      rw [hds, hdt] at hr
      have hrlt : r < ε := lt_of_le_of_lt hr.2 (max_lt hs.2 ht.2)
      exact le_of_lt (H2 r ⟨hr.1, lt_of_lt_of_le hrlt hεe2⟩ t
        ⟨ht.1, lt_of_lt_of_le ht.2 hεe2⟩)
  have hev := key2 (fun s t => comparisonAngle p (c' s) (c'' t)
    ≤ (alexandrovAngle p c c' + δ / 4) + (alexandrovAngle p c c'' + δ / 4)) ε hε main
  have hfin : alexandrovAngle p c' c''
      ≤ (alexandrovAngle p c c' + δ / 4) + (alexandrovAngle p c c'' + δ / 4) :=
    Filter.limsup_le_of_le (hcob c' c'') hev
  linarith
