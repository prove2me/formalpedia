-- Prove2me | solution 1 for ManyServerQED.Scheduling.asymptotic_modulus_transfers_uniform_random_clock_evaluations
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:26:06.46589+00:00
-- url     : https://prove2.me/submissions/c90fb961-54f3-49c2-9c9a-1a1f7df79d19

import Mathlib

open Filter Topology Set MeasureTheory
open scoped ENNReal

theorem solution {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] (P : Measure Ω)
    (X : ℕ → Ω → ℝ → E)
    (h : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ dist (X n ω s) (X n ω t)} ≤ ENNReal.ofReal η)
    (u v : ℕ → Ω → ℝ → ℝ) (T : ℝ)
    (hu : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → 0 ≤ u n ω t)
    (hv : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → v n ω t ∈ Icc (0:ℝ) T)
    (hUV : ∀ δ > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
      δ ≤ |u n ω t-v n ω t|}) atTop (𝓝 0)) :
    ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
      ε ≤ dist (X n ω (u n ω t)) (X n ω (v n ω t))}) atTop (𝓝 0) := by
  intro ε hε
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨e,_,he,hηe⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hE := ENNReal.ofReal_pos.1 he
  obtain ⟨T',hT'⟩ := exists_nat_gt (T+1)
  obtain ⟨δ,hδ,hMd⟩ := h T' ε (e/2) hε (by positivity)
  let d := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hs := (tendsto_order.1 (hUV d hd)).2 (ENNReal.ofReal (e/2))
    (ENNReal.ofReal_pos.2 (by positivity))
  let U (n : ℕ) := {ω | ∃ t ∈ Icc (0:ℝ) T, d ≤ |u n ω t-v n ω t|}
  let V (n : ℕ) := {ω | ∃ s ∈ Icc (0:ℝ) (T':ℝ), ∃ t ∈ Icc (0:ℝ) (T':ℝ),
    |s-t| ≤ δ ∧ ε ≤ dist (X n ω s) (X n ω t)}
  filter_upwards [hMd,hs,hu,hv] with n hn hn' hu hv
  calc
    _ ≤ P (U n ∪ V n) := by
      apply measure_mono
      rintro ω ⟨t,ht,hω⟩
      by_cases hbad : d ≤ |u n ω t-v n ω t|
      · exact Or.inl ⟨t,ht,hbad⟩
      · have hlt := lt_of_not_ge hbad
        have hlt' := lt_of_lt_of_le hlt (min_le_right δ 1)
        have hbound : u n ω t ≤ T+1 := by linarith [(abs_lt.1 hlt').2,(hv ω t ht).2]
        exact Or.inr ⟨u n ω t,⟨hu ω t ht,hbound.trans hT'.le⟩,
          v n ω t,⟨(hv ω t ht).1,by linarith [(hv ω t ht).2]⟩,
          hlt.le.trans (min_le_left δ 1),hω⟩
    _ ≤ P (U n) + P (V n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (e/2) + ENNReal.ofReal (e/2) := add_le_add hn'.le hn
    _ = ENNReal.ofReal e := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ η := hηe.le
