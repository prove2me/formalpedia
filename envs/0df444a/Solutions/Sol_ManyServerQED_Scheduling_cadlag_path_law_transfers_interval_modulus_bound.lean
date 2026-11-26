-- Prove2me | solution 1 for ManyServerQED.Scheduling.cadlag_path_law_transfers_interval_modulus_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:40:29.82209+00:00
-- url     : https://prove2.me/submissions/b5f543c3-0642-4395-87e7-f9de2f4f15d6

import Mathlib

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

private theorem rational_right_approximation {E : Type*} [PseudoMetricSpace E]
    {x : ℝ → E} {T : ℕ}
    (h : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt x (Ici s) s)
    {s e : ℝ} (hs : s ∈ Icc (0:ℝ) (T:ℝ)) (he : 0 < e) :
    ∃ q : ℚ, (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ dist (q:ℝ) s < e ∧ dist (x q) (x s) < e := by
  rcases hs.2.lt_or_eq with hst | hst
  · obtain ⟨d,hd,hD⟩ := Metric.continuousWithinAt_iff.1 (h s hs.1) e he
    have hm : s < min (T:ℝ) (s+min d e) := lt_min hst
      (lt_add_of_pos_right _ (lt_min hd he))
    obtain ⟨q,hq,hQ⟩ := exists_rat_btwn hm
    have hdQ : dist (q:ℝ) s < min d e := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 hq)]
      linarith [(lt_min_iff.1 hQ).2]
    exact ⟨q,⟨hs.1.trans hq.le,(lt_min_iff.1 hQ).1.le⟩,(lt_min_iff.1 hdQ).2,
      hD hq.le (lt_min_iff.1 hdQ).1⟩
  · have hu : ((T:ℚ):ℝ) = s := by simpa using hst.symm
    exact ⟨T,by rw [hu]; exact hs,by rw [hu,dist_self]; exact he,
      by rw [hu,dist_self]; exact he⟩

theorem solution {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {P' : Measure Ω'}
    (X : Ω → ℝ → E) (Y : Ω' → ℝ → E)
    (hLaw : IdentDistrib (fun ω (t : ℝ≥0) => X ω t) (fun ω (t : ℝ≥0) => Y ω t) P P')
    (hX : ∀ ω s, 0 ≤ s → ContinuousWithinAt (X ω) (Ici s) s)
    (T : ℕ) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ δ ∧ ε ≤ dist (X ω s) (X ω t)} ≤
    P' {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ 2*δ ∧ ε/2 ≤ dist (Y ω s) (Y ω t)} := by
  let B : Set (ℝ≥0 → E) := {f | ∃ (q r : ℚ), (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
    (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
    ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)}
  have hB : MeasurableSet B := by
    have he : B = ⋃ q : ℚ, ⋃ r : ℚ, {f | (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
        (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
        ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)} := by ext; simp [B]
    rw [he]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun r => ?_
    by_cases c : (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
        |(q:ℝ)-(r:ℝ)| < 2*δ
    · simpa only [c.1,c.2.1,c.2.2,true_and] using
        (measurableSet_lt (measurable_const (a := ε/2))
          ((measurable_pi_apply (q:ℝ).toNNReal).dist (measurable_pi_apply (r:ℝ).toNNReal)) :
          MeasurableSet {f : ℝ≥0 → E | ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)})
    · have hf : {f : ℝ≥0 → E | (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
          (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
          ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)} = ∅ := by
        ext f
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => c ⟨h.1,h.2.1,h.2.2.1⟩
      rw [hf]
      exact MeasurableSet.empty
  let F (ω : Ω) (t : ℝ≥0) := X ω t
  let G (ω : Ω') (t : ℝ≥0) := Y ω t
  have hMeasure : P (F ⁻¹' B) = P' (G ⁻¹' B) := by
    rw [← Measure.map_apply_of_aemeasurable hLaw.aemeasurable_fst hB,
      ← Measure.map_apply_of_aemeasurable hLaw.aemeasurable_snd hB]
    exact congrArg (fun m : Measure (ℝ≥0 → E) => m B) hLaw.map_eq
  calc
    _ ≤ P (F ⁻¹' B) := by
      apply measure_mono
      rintro ω ⟨s,hs,t,ht,hst,hval⟩
      let e := min (δ/4) (ε/8)
      have he : 0 < e := lt_min (by positivity) (by positivity)
      obtain ⟨q,hq,hqs,hQ⟩ := rational_right_approximation (hX ω) hs he
      obtain ⟨r,hr,hrt,hR⟩ := rational_right_approximation (hX ω) ht he
      have hT : |(q:ℝ)-(r:ℝ)| < 2*δ := by
        have h1 := dist_triangle (q:ℝ) s (r:ℝ)
        have h2 := dist_triangle s t (r:ℝ)
        rw [dist_comm t (r:ℝ)] at h2
        rw [← Real.dist_eq] at hst ⊢
        have he' : e ≤ δ/4 := min_le_left _ _
        linarith only [h1,h2,hst,hqs,hrt,he',hδ]
      have hv : ε/2 < dist (X ω q) (X ω r) := by
        have h1 := dist_triangle (X ω s) (X ω q) (X ω t)
        have h2 := dist_triangle (X ω q) (X ω r) (X ω t)
        rw [dist_comm (X ω s) (X ω q)] at h1
        have he' : e ≤ ε/8 := min_le_right _ _
        linarith only [h1,h2,hval,hQ,hR,he',hε]
      refine ⟨q,r,hq,hr,hT,?_⟩
      simpa only [F,Real.coe_toNNReal _ hq.1,Real.coe_toNNReal _ hr.1] using hv
    _ = P' (G ⁻¹' B) := hMeasure
    _ ≤ _ := by
      apply measure_mono
      rintro ω ⟨q,r,hq,hr,hd,hv⟩
      refine ⟨q,hq,r,hr,hd.le,?_⟩
      simpa only [G,Real.coe_toNNReal _ hq.1,Real.coe_toNNReal _ hr.1] using hv.le
