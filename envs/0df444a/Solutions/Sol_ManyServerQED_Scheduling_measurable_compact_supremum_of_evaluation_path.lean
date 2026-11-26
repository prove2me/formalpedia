-- Prove2me | solution 1 for ManyServerQED.Scheduling.measurable_compact_supremum_of_evaluation_path
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:14.68729+00:00
-- url     : https://prove2.me/submissions/b606ffb9-eb59-4a66-abbc-b0b700916a1a

import Mathlib

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

private theorem rational_right_approximation (t T : ℝ) (htT : t < T) :
    ∃ q : ℕ → ℚ, Tendsto (fun j => (q j:ℝ)) atTop (𝓝[Ici t] t) ∧
      ∀ j, t < (q j:ℝ) ∧ (q j:ℝ) < T := by
  have hchoose (j : ℕ) : ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min T (t + 1 / (j + 1 : ℝ)) :=
    exists_rat_btwn (lt_min htT (lt_add_of_pos_right _ (by positivity)))
  choose q hq using hchoose
  have hub (j : ℕ) : (q j : ℝ) ≤ t + 1 / (j + 1 : ℝ) :=
    (hq j).2.le.trans (min_le_right _ _)
  have hlb (j : ℕ) : t ≤ (q j : ℝ) := (hq j).1.le
  have hInv : Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) atTop (𝓝 0) := by
    have hn : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hn' : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
      tendsto_atTop.2 (fun b => ((tendsto_atTop.1 hn) b).mono (fun _ h => by linarith))
    exact tendsto_const_nhds.div_atTop hn'
  have hUp : Tendsto (fun j : ℕ => t + 1 / (j + 1 : ℝ)) atTop (𝓝 t) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := t)).add hInv
  have hqT : Tendsto (fun j : ℕ => (q j : ℝ)) atTop (𝓝[Ici t] t) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUp hlb hub,
      Eventually.of_forall hlb⟩

  exact ⟨q,hqT,fun j => ⟨(hq j).1,(hq j).2.trans_le (min_le_left _ _)⟩⟩

set_option maxHeartbeats 1250000 in
theorem solution {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (v : E → ℝ) (hv : Continuous v) (T : ℝ≥0) :
    ∃ S : (ℝ≥0 → E) → ℝ≥0∞, Measurable S ∧ ∀ f : ℝ → E,
      (∀ t, 0 ≤ t → ContinuousWithinAt f (Ici t) t) →
      S (fun t : ℝ≥0 => f t) = ⨆ t : ℝ, ⨆ (_ : t ∈ Icc (0:ℝ) T), ENNReal.ofReal (v (f t)) := by
  classical
  let S (x : ℝ≥0 → E) := max
    (⨆ q : ℚ, if (q : ℝ) ∈ Icc (0:ℝ) T then ENNReal.ofReal (v (x (q:ℝ).toNNReal)) else 0)
    (ENNReal.ofReal (v (x T)))
  refine ⟨S,?_ ,?_⟩
  · apply Measurable.max
    · apply Measurable.iSup
      intro q
      split_ifs
      · exact ENNReal.measurable_ofReal.comp (hv.measurable.comp (measurable_pi_apply _))
      · exact measurable_const
    · exact ENNReal.measurable_ofReal.comp (hv.measurable.comp (measurable_pi_apply _))
  · intro f hf
    have hEq (q : ℚ) (hq : (q:ℝ) ∈ Icc (0:ℝ) T) : ((q:ℝ).toNNReal:ℝ) = (q:ℝ) :=
      Real.coe_toNNReal _ hq.1
    unfold S
    simp_rw [show ∀ q : ℚ,
      (if (q : ℝ) ∈ Icc (0:ℝ) T then ENNReal.ofReal (v (f ((q:ℝ).toNNReal:ℝ))) else 0) =
      (if (q : ℝ) ∈ Icc (0:ℝ) T then ENNReal.ofReal (v (f (q:ℝ))) else 0) from
        fun q => by
          split_ifs with h
          · rw [hEq q h]
          · rfl]
    apply le_antisymm
    · apply max_le
      · apply iSup_le
        intro q
        split_ifs with h
        · exact le_iSup₂_of_le (q : ℝ) h le_rfl
        · exact bot_le
      · exact le_iSup₂_of_le (T:ℝ) ⟨T.2,le_rfl⟩ le_rfl
    · apply iSup₂_le
      intro t ht
      by_cases h : t = (T:ℝ)
      · exact h ▸ le_max_right _ _
      have htT : t < (T:ℝ) := lt_of_le_of_ne ht.2 h
      obtain ⟨q,hqT,hq⟩ := rational_right_approximation t T htT
      have hL : Tendsto (fun j => ENNReal.ofReal (v (f (q j)))) atTop
          (𝓝 (ENNReal.ofReal (v (f t)))) :=
        ((ENNReal.continuous_ofReal.comp hv).continuousAt.comp_continuousWithinAt
          (hf t ht.1)).tendsto.comp hqT
      refine le_of_tendsto hL (Eventually.of_forall fun j => ?_)
      have hqI : (q j : ℝ) ∈ Icc (0:ℝ) T := ⟨ht.1.trans (hq j).1.le,(hq j).2.le⟩
      apply le_trans _ (le_max_left _ _)
      have hi := le_iSup (fun q : ℚ => if (q:ℝ) ∈ Icc (0:ℝ) T
        then ENNReal.ofReal (v (f (q:ℝ))) else 0) (q j)
      rwa [if_pos hqI] at hi
