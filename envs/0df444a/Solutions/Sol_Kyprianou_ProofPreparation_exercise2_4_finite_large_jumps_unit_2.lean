-- Prove2me | solution 2 for Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:17:47.073264+00:00
-- url     : https://prove2.me/submissions/cbd3f9d9-6249-48d1-9c0e-7fffd3dd351e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem finite_large_jumps_of_nnreal_cadlag
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l))
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l) ∧
        δ < |Y u - l|}.Finite := by
  set A := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l) ∧ δ < |Y u - l|} with hA
  -- a point of A cannot lie in a window where Y stays within δ/3 of a constant c
  have key : ∀ (u : ℝ≥0) (c : ℝ) (W : Set ℝ≥0), u ∈ A → W ∈ 𝓝[<] u →
      (∀ v ∈ W, |Y v - c| < δ / 3) → |Y u - c| < δ / 3 → False := by
    intro u c W hu hW hWc huc
    obtain ⟨hu0, -, l, hl, hjump⟩ := hu
    haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
    have hb : ∀ᶠ v in 𝓝[<] u, |Y v - c| ≤ δ / 3 :=
      Filter.mem_of_superset hW fun v hv => (hWc v hv).le
    have hlc : |l - c| ≤ δ / 3 := le_of_tendsto ((hl.sub_const c).abs) hb
    have : |Y u - l| ≤ |Y u - c| + |l - c| := by
      calc |Y u - l| = |(Y u - c) - (l - c)| := by ring_nf
        _ ≤ |Y u - c| + |l - c| := abs_sub _ _
    linarith
  by_contra hinf
  obtain ⟨s, -, hs⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ≥0) T)) (fun u hu => ⟨bot_le, hu.2.1⟩)
  rw [accPt_iff_frequently_nhdsNE] at hs
  apply hs
  rw [← nhdsLT_sup_nhdsGT, eventually_sup]
  constructor
  · -- left of s
    rcases eq_or_lt_of_le (bot_le : (0:ℝ≥0) ≤ s) with h0 | hs0
    · subst h0
      rw [Set.Iio_bot, nhdsWithin_empty]
      exact Filter.eventually_bot
    · obtain ⟨L, hLs⟩ := hL s hs0
      have hG : ∀ᶠ v in 𝓝[<] s, |Y v - L| < δ / 3 := by
        have := hLs.eventually (Metric.ball_mem_nhds L (by positivity : (0:ℝ) < δ / 3))
        filter_upwards [this] with v hv
        simpa [Real.dist_eq] using hv
      obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs0).1 hG
      filter_upwards [Ioo_mem_nhdsLT ha] with u hu huA
      exact key u L (Ioo a u) huA (Ioo_mem_nhdsLT hu.1)
        (fun v hv => hsub ⟨hv.1, hv.2.trans hu.2⟩) (hsub hu)
  · -- right of s
    have hG : ∀ᶠ v in 𝓝[≥] s, |Y v - Y s| < δ / 3 := by
      have := (hR s).eventually (Metric.ball_mem_nhds (Y s) (by positivity : (0:ℝ) < δ / 3))
      filter_upwards [this] with v hv
      simpa [Real.dist_eq] using hv
    obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hG
    filter_upwards [Ioo_mem_nhdsGT hb] with u hu huA
    exact key u (Y s) (Ioo s u) huA (Ioo_mem_nhdsLT hu.1)
      (fun v hv => hsub ⟨hv.1.le, hv.2.trans hu.2⟩) (hsub ⟨hu.1.le, hu.2⟩)
theorem nnreal_coe_tendsto_left (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact NNReal.coe_lt_coe.2 hu
theorem real_unit_large_jumps_finite_of_nnreal_extension
    (f : ℝ → ℝ) (Y : ℝ≥0 → ℝ)
    (heq : ∀ u : ℝ≥0, u ≤ 1 → Y u = f (u : ℝ))
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Set.Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l))
    (c : ℝ) (hc : 0 < c) :
    Set.Finite {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧ c < |f t - l|} := by
  apply ((finite_large_jumps_of_nnreal_cadlag Y hR hL 1 c hc).image (fun u : ℝ≥0 => (u : ℝ))).subset
  rintro t ⟨⟨ht0, ht1⟩, l, hl, hjump⟩
  refine ⟨⟨t, ht0.le⟩, ⟨?_, ?_, l, ?_, ?_⟩, rfl⟩
  · exact_mod_cast ht0
  · exact_mod_cast ht1
  · have hc' := nnreal_coe_tendsto_left ⟨t, ht0.le⟩
    refine (hl.comp hc').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv1 : v ≤ 1 := by
      have : (v : ℝ) < t := hv
      exact_mod_cast (this.le.trans ht1)
    simp [Function.comp, heq v hv1]
  · have h1 : (⟨t, ht0.le⟩ : ℝ≥0) ≤ 1 := by
      change t ≤ 1
      exact ht1
    rw [heq _ h1]
    exact hjump
theorem nnreal_clipped_right_continuous
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t) :
    ∀ u : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => f (min (v : ℝ) 1)) (Set.Ici u) u := by
  intro u
  have ht : min (u : ℝ) 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨le_min u.2 zero_le_one, min_le_right _ _⟩
  have hg : ContinuousWithinAt (fun v : ℝ≥0 => min (v : ℝ) 1) (Set.Ici u) u :=
    (NNReal.continuous_coe.min continuous_const).continuousWithinAt
  refine ContinuousWithinAt.comp (g := f) (hR _ ht) hg ?_
  intro v hv
  simp only [Set.mem_Ici] at hv
  exact ⟨min_le_min (NNReal.coe_le_coe.2 hv) le_rfl, min_le_right _ _⟩
theorem nnreal_clipped_left_limit_exists
    (f : ℝ → ℝ)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => f (min (v : ℝ) 1))
        (𝓝[<] u) (𝓝 l) := by
  intro u hu
  by_cases h1 : (u : ℝ) ≤ 1
  · obtain ⟨l, hl⟩ := hL u ⟨by exact_mod_cast hu, h1⟩
    refine ⟨l, ?_⟩
    have hc : Tendsto (fun v : ℝ≥0 => (v : ℝ)) (𝓝[<] u) (𝓝[<] (u : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (NNReal.continuous_coe.tendsto u).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact NNReal.coe_lt_coe.2 hv
    refine (hl.comp hc).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have : (v : ℝ) ≤ 1 := (NNReal.coe_lt_coe.2 hv).le.trans h1
    simp [Function.comp, min_eq_left this]
  · rw [not_le] at h1
    refine ⟨f 1, ?_⟩
    apply tendsto_const_nhds.congr'
    have h1' : (1 : ℝ≥0) < u := by exact_mod_cast h1
    filter_upwards [Ioo_mem_nhdsLT h1'] with v hv
    have : (1 : ℝ) ≤ v := by exact_mod_cast hv.1.le
    simp [min_eq_right this]
theorem exercise2_4_finite_large_jumps_unit
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ c : ℝ, 0 < c →
      Set.Finite {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
        ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧
          c < |f t - l|} := by
  intro c hc
  apply real_unit_large_jumps_finite_of_nnreal_extension f (fun v : ℝ≥0 => f (min (v : ℝ) 1))
    _ (nnreal_clipped_right_continuous f hR) (nnreal_clipped_left_limit_exists f hL) c hc
  intro u hu
  have : (u : ℝ) ≤ 1 := by exact_mod_cast hu
  simp [min_eq_left this]

end Kyprianou.ProofPreparation

theorem solution
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ c : ℝ, 0 < c →
      Set.Finite {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧
        ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧
          c < |f t - l|} := by
  first
  | exact Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit
  | exact Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit ..
  | (apply Kyprianou.ProofPreparation.exercise2_4_finite_large_jumps_unit <;> assumption)
