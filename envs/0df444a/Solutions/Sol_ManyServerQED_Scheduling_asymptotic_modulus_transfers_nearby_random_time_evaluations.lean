-- Prove2me | solution 1 for ManyServerQED.Scheduling.asymptotic_modulus_transfers_nearby_random_time_evaluations
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:00:32.267476+00:00
-- url     : https://prove2.me/submissions/615c6da9-6fec-443b-8a19-5613804f7894

import Mathlib

open Filter Topology Set MeasureTheory
open scoped ENNReal

theorem solution {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] (P : Measure Ω)
    (X : ℕ → Ω → ℝ → E)
    (h : ∀ (T : ℝ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        ε ≤ dist (X n ω s) (X n ω t)} ≤ ENNReal.ofReal η)
    (u v : ℕ → Ω → ℝ) (T : ℝ)
    (hu : ∀ n ω, 0 ≤ u n ω) (hv : ∀ n ω, v n ω ∈ Icc (0:ℝ) T)
    (hUV : ∀ δ > (0:ℝ), Tendsto (fun n => P {ω | δ ≤ |u n ω-v n ω|}) atTop (𝓝 0)) :
    ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ε ≤ dist (X n ω (u n ω)) (X n ω (v n ω))})
      atTop (𝓝 0) := by
  intro ε hε
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨e,_,he,hηe⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hE := ENNReal.ofReal_pos.1 he
  obtain ⟨δ,hδ,hMd⟩ := h (T+1) ε (e/2) hε (by positivity)
  let d := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hs := (tendsto_order.1 (hUV d hd)).2 (ENNReal.ofReal (e/2))
    (ENNReal.ofReal_pos.2 (by positivity))
  let U (n : ℕ) := {ω | d ≤ |u n ω-v n ω|}
  let V (n : ℕ) := {ω | ∃ s ∈ Icc (0:ℝ) (T+1), ∃ t ∈ Icc (0:ℝ) (T+1),
    |s-t| ≤ δ ∧ ε ≤ dist (X n ω s) (X n ω t)}
  filter_upwards [hMd,hs] with n hn hn'
  calc
    _ ≤ P (U n ∪ V n) := by
      apply measure_mono
      intro ω hω
      by_cases hbad : d ≤ |u n ω-v n ω|
      · exact Or.inl hbad
      · have hlt := lt_of_not_ge hbad
        have hlt' := lt_of_lt_of_le hlt (min_le_right δ 1)
        have hbound : u n ω ≤ T+1 := by linarith [(abs_lt.1 hlt').2,(hv n ω).2]
        exact Or.inr ⟨u n ω,⟨hu n ω,hbound⟩,v n ω,⟨(hv n ω).1,by linarith [(hv n ω).2]⟩,
          hlt.le.trans (min_le_left δ 1),hω⟩
    _ ≤ P (U n) + P (V n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (e/2) + ENNReal.ofReal (e/2) := add_le_add hn'.le hn
    _ = ENNReal.ofReal e := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ η := hηe.le
