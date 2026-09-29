-- Prove2me | solution 1 for MetricGeometry.limsup_comparisonAngle_le_alexandrovAngle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T01:18:43.620356+00:00
-- url     : https://prove2.me/submissions/34b04979-ea8b-459b-ae0e-253dbb237e70

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_mem_Icc
import Theorems.Thm_MetricGeometry_cos_comparisonAngle_bounds

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X]
    (p : X) (c c' : ℝ → X) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : ∀ s ∈ Set.Ioc (0:ℝ) a, dist p (c s) = s)
    (hc'0 : c' 0 = p)
    (hc' : ∀ r ∈ Set.Icc (0:ℝ) b, ∀ r' ∈ Set.Icc (0:ℝ) b,
      dist (c' r) (c' r') = |r - r'|)
    (t : ℝ) (ht : 0 < t) (htb : t ≤ b) :
    Filter.limsup (fun s : ℝ => comparisonAngle p (c s) (c' t)) (𝓝[>] (0:ℝ))
      ≤ alexandrovAngle p c c' := by
  set F : Filter (ℝ × ℝ) := (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)) with hF
  have hNeBot : F.NeBot := by rw [hF]; infer_instance
  haveI := hNeBot
  -- distances along c'
  have hdc' : ∀ r ∈ Set.Icc (0:ℝ) b, dist p (c' r) = r := by
    intro r hr
    have := hc' 0 ⟨le_refl 0, hb.le⟩ r hr
    rw [hc'0] at this
    rw [this, abs_of_nonpos (by linarith [hr.1]), neg_sub, sub_zero]
  -- boundedness helpers
  have hbdF : ∀ g1 g2 : ℝ → X, IsBoundedUnder (· ≤ ·) F
      (fun st : ℝ × ℝ => comparisonAngle p (g1 st.1) (g2 st.2)) :=
    fun g1 g2 => Filter.isBoundedUnder_of
      ⟨Real.pi, fun st => (MetricGeometry.comparisonAngle_mem_Icc p (g1 st.1) (g2 st.2)).2⟩
  have hcob1 : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0:ℝ))
      (fun s : ℝ => comparisonAngle p (c s) (c' t)) :=
    IsBoundedUnder.isCoboundedUnder_le (Filter.isBoundedUnder_of
      ⟨0, fun s => (MetricGeometry.comparisonAngle_mem_Icc p (c s) (c' t)).1⟩)
  have hnn : 0 ≤ alexandrovAngle p c c' := by
    have h0 : Filter.limsup (fun _ : ℝ × ℝ => (0:ℝ)) F = 0 := Filter.limsup_const 0
    have hle : Filter.limsup (fun _ : ℝ × ℝ => (0:ℝ)) F
        ≤ Filter.limsup (fun st : ℝ × ℝ => comparisonAngle p (c st.1) (c' st.2)) F :=
      Filter.limsup_le_limsup
        (Eventually.of_forall fun st =>
          (MetricGeometry.comparisonAngle_mem_Icc p (c st.1) (c' st.2)).1)
        (IsBoundedUnder.isCoboundedUnder_le
          (Filter.isBoundedUnder_of ⟨0, fun _ : ℝ × ℝ => le_refl (0:ℝ)⟩))
        (hbdF c c')
    rw [h0] at hle
    exact hle
  have key : ∀ Q : ℝ → ℝ → Prop, (∀ᶠ st in F, Q st.1 st.2) →
      ∃ ε > (0:ℝ), ∀ s ∈ Set.Ioo (0:ℝ) ε, ∀ r ∈ Set.Ioo (0:ℝ) ε, Q s r := by
    intro Q hQ
    rw [hF, Filter.eventually_prod_iff] at hQ
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := hQ
    obtain ⟨u1, hu1, hs1⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpa
    obtain ⟨u2, hu2, hs2⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpb
    refine ⟨min u1 u2, lt_min hu1 hu2, fun s hs r hr => ?_⟩
    exact hab (hs1 ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
      (hs2 ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩)
  -- the comparison of cosines along c'
  have hmono : ∀ s : ℝ, 0 < s → s ≤ a → ∀ r : ℝ, 0 < r → r ≤ t →
      Real.cos (comparisonAngle p (c s) (c' r))
        ≤ Real.cos (comparisonAngle p (c s) (c' t)) + s / (2 * r) := by
    intro s hs hsa r hr hrt
    have hrb : r ∈ Set.Icc (0:ℝ) b := ⟨hr.le, le_trans hrt htb⟩
    have htbb : t ∈ Set.Icc (0:ℝ) b := ⟨ht.le, htb⟩
    have hcs : dist p (c s) = s := hc s ⟨hs, hsa⟩
    have hub := (MetricGeometry.cos_comparisonAngle_bounds p (c s) (c' r) s r hs hr
      hcs (hdc' r hrb)).2
    have hlb := (MetricGeometry.cos_comparisonAngle_bounds p (c s) (c' t) s t hs ht
      hcs (hdc' t htbb)).1
    -- triangle inequality: r - d(c s, c' r) ≤ t - d(c s, c' t)
    have hstep : dist (c s) (c' t) ≤ dist (c s) (c' r) + (t - r) := by
      have := dist_triangle (c s) (c' r) (c' t)
      have hrr : dist (c' r) (c' t) = t - r := by
        rw [hc' r hrb t htbb, abs_of_nonpos (by linarith)]; ring
      rw [hrr] at this
      linarith
    have hnum : r - dist (c s) (c' r) ≤ t - dist (c s) (c' t) := by linarith
    have hdiv : (r - dist (c s) (c' r)) / s ≤ (t - dist (c s) (c' t)) / s :=
      div_le_div_of_nonneg_right hnum hs.le
    linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  by_cases hcase : Real.pi ≤ alexandrovAngle p c c' + η
  · refine Filter.limsup_le_of_le hcob1 (Eventually.of_forall fun s => ?_)
    exact le_trans (MetricGeometry.comparisonAngle_mem_Icc p (c s) (c' t)).2 hcase
  push_neg at hcase
  set δ := η / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hApi : alexandrovAngle p c c' + 2 * δ ≤ Real.pi := by rw [hδdef]; linarith
  have hκ : 0 < Real.cos (alexandrovAngle p c c' + δ)
      - Real.cos (alexandrovAngle p c c' + 2 * δ) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := alexandrovAngle p c c' + δ) (y := alexandrovAngle p c c' + 2 * δ)
      (by linarith) hApi (by linarith)
    linarith
  have e1 : ∀ᶠ st in F,
      comparisonAngle p (c st.1) (c' st.2) < alexandrovAngle p c c' + δ :=
    Filter.eventually_lt_of_limsup_lt (by
      show alexandrovAngle p c c' < alexandrovAngle p c c' + δ
      linarith) (hbdF c c')
  obtain ⟨ε1, hε1, H1⟩ := key
    (fun s r => comparisonAngle p (c s) (c' r) < alexandrovAngle p c c' + δ) e1
  set r0 := min (min (ε1 / 2) t) b with hr0def
  have hr0 : 0 < r0 := lt_min (lt_min (by linarith) ht) hb
  have hr0t : r0 ≤ t := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr0e : r0 < ε1 := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
    (by linarith)
  set κ := Real.cos (alexandrovAngle p c c' + δ)
      - Real.cos (alexandrovAngle p c c' + 2 * δ) with hκdef
  set S := min (min ε1 a) (2 * r0 * κ) with hSdef
  have hS : 0 < S := lt_min (lt_min hε1 ha) (by positivity)
  refine Filter.limsup_le_of_le hcob1 ?_
  have hmem : Set.Ioo (0:ℝ) S ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hS
  refine Filter.eventually_of_mem hmem fun s hs => ?_
  have hs0 : 0 < s := hs.1
  have hsa : s ≤ a := le_of_lt (lt_of_lt_of_le hs.2 (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hse : s < ε1 := lt_of_lt_of_le hs.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hsk : s < 2 * r0 * κ := lt_of_lt_of_le hs.2 (min_le_right _ _)
  -- the angle at (s, r0) is small
  have hsmall : comparisonAngle p (c s) (c' r0) < alexandrovAngle p c c' + δ :=
    H1 s ⟨hs0, hse⟩ r0 ⟨hr0, hr0e⟩
  have hcosge : Real.cos (alexandrovAngle p c c' + δ)
      ≤ Real.cos (comparisonAngle p (c s) (c' r0)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (MetricGeometry.comparisonAngle_mem_Icc p (c s) (c' r0)).1
      (by linarith) hsmall.le
  have hbound := hmono s hs0 hsa r0 hr0 hr0t
  have hfrac : s / (2 * r0) < κ := by
    rw [div_lt_iff₀ (by positivity)]
    linarith [hsk]
  have hgt : Real.cos (alexandrovAngle p c c' + 2 * δ)
      < Real.cos (comparisonAngle p (c s) (c' t)) := by
    rw [hκdef] at hfrac
    linarith
  by_contra hcon
  push_neg at hcon
  have hle2 : alexandrovAngle p c c' + 2 * δ ≤ comparisonAngle p (c s) (c' t) := by
    rw [hδdef]; linarith
  have hc2 := Real.cos_le_cos_of_nonneg_of_le_pi
    (x := alexandrovAngle p c c' + 2 * δ) (y := comparisonAngle p (c s) (c' t))
    (by linarith) (MetricGeometry.comparisonAngle_mem_Icc p (c s) (c' t)).2 hle2
  linarith
