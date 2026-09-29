-- Prove2me | solution 1 for MilnorDynamics.diverging_subseq_tendsto_puncture
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:43:55.847894+00:00
-- url     : https://prove2.me/submissions/ede54a52-7552-4f63-acd7-7e814e850440

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- Core step: on a compact preconnected set, pointwise control at one point propagates. -/
theorem aux_dsp_core (U : Set ℂ) (g : ℕ → ℂ → ℂ) (hg : ∀ n, ContinuousOn (g n) U)
    (V W : ℝ → Set ℂ)
    (hVo : ∀ ε, 0 < ε → IsOpen (V ε)) (hWo : ∀ ε, 0 < ε → IsOpen (W ε))
    (hVm : ∀ ε, 0 < ε → ε ≤ 1/4 → V ε ⊆ V (1/4))
    (hWm : ∀ ε, 0 < ε → ε ≤ 1/4 → W ε ⊆ W (1/4))
    (hdisj : Disjoint (V (1/4)) (W (1/4)))
    (hcov : ∀ K ⊆ U, IsCompact K → ∀ ε, 0 < ε → ε ≤ 1/4 →
      ∀ᶠ n in atTop, ∀ x ∈ K, g n x ∈ V ε ∪ W ε)
    (K : Set ℂ) (hKU : K ⊆ U) (hK : IsCompact K) (hKc : IsPreconnected K)
    (w : ℂ) (hw : w ∈ K) (hgw : ∀ᶠ n in atTop, g n w ∈ V (1/4)) :
    ∀ ε, 0 < ε → ε ≤ 1/4 → ∀ᶠ n in atTop, ∀ x ∈ K, g n x ∈ V ε := by
  intro ε hε hε4
  filter_upwards [hcov K hKU hK ε hε hε4, hgw] with n hn hnw
  have himg : IsPreconnected (g n '' K) := hKc.image _ ((hg n).mono hKU)
  have hsub : g n '' K ⊆ V ε ∪ W ε := by
    rintro _ ⟨x, hx, rfl⟩; exact hn x hx
  have hwV : g n w ∈ V ε := by
    rcases hn w hw with h | h
    · exact h
    · exact absurd (hWm ε hε hε4 h) (Set.disjoint_left.mp hdisj hnw)
  have hdisj' : Disjoint (V ε) (W ε) :=
    Disjoint.mono (hVm ε hε hε4) (hWm ε hε hε4) hdisj
  have := himg.subset_left_of_subset_union (hVo ε hε) (hWo ε hε) hdisj' hsub
    ⟨g n w, ⟨w, hw, rfl⟩, hwV⟩
  intro x hx
  exact this ⟨x, hx, rfl⟩

/-- Global step: uniform control on every compact subset of a connected open set. -/
theorem aux_dsp_global (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (g : ℕ → ℂ → ℂ) (hg : ∀ n, ContinuousOn (g n) U)
    (V W : ℝ → Set ℂ)
    (hVo : ∀ ε, 0 < ε → IsOpen (V ε)) (hWo : ∀ ε, 0 < ε → IsOpen (W ε))
    (hVm : ∀ ε, 0 < ε → ε ≤ 1/4 → V ε ⊆ V (1/4))
    (hWm : ∀ ε, 0 < ε → ε ≤ 1/4 → W ε ⊆ W (1/4))
    (hdisj : Disjoint (V (1/4)) (W (1/4)))
    (hcov : ∀ K ⊆ U, IsCompact K → ∀ ε, 0 < ε → ε ≤ 1/4 →
      ∀ᶠ n in atTop, ∀ x ∈ K, g n x ∈ V ε ∪ W ε)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hgz : ∀ᶠ n in atTop, g n z₀ ∈ V (1/4)) :
    ∀ K ⊆ U, IsCompact K → ∀ ε, 0 < ε → ε ≤ 1/4 →
      ∀ᶠ n in atTop, ∀ x ∈ K, g n x ∈ V ε := by
  have hball : ∀ z ∈ U, ∃ r > 0, Metric.closedBall z r ⊆ U := by
    intro z hz
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨r / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩
  let u : Set ℂ := {z | ∃ t ∈ nhds z, ∀ ε, 0 < ε → ε ≤ 1/4 →
    ∀ᶠ n in atTop, ∀ x ∈ t, g n x ∈ V ε}
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨t, ht, hP⟩
    filter_upwards [eventually_mem_nhds_iff.mpr ht] with z' hz'
    exact ⟨t, hz', hP⟩
  have key : ∀ z w : ℂ, ∀ r > 0, Metric.closedBall z r ⊆ U → w ∈ Metric.closedBall z r →
      (∀ᶠ n in atTop, g n w ∈ V (1/4)) → z ∈ u := by
    intro z w r hr hrU hw hgw
    refine ⟨Metric.closedBall z r, Metric.closedBall_mem_nhds z hr, ?_⟩
    exact aux_dsp_core U g hg V W hVo hWo hVm hWm hdisj hcov _ hrU (isCompact_closedBall z r)
      (convex_closedBall z r).isPreconnected w hw hgw
  have hUu : U ⊆ u := by
    refine hUc.subset_of_closure_inter_subset hu_open ?_ ?_
    · obtain ⟨r, hr, hrU⟩ := hball z₀ hz₀
      exact ⟨z₀, hz₀, key z₀ z₀ r hr hrU (Metric.mem_closedBall_self hr.le) hgz⟩
    · rintro z ⟨hzc, hzU⟩
      obtain ⟨r, hr, hrU⟩ := hball z hzU
      obtain ⟨w, hwball, hwu⟩ := mem_closure_iff_nhds.mp hzc _ (Metric.ball_mem_nhds z hr)
      obtain ⟨t, ht, hP⟩ := hwu
      have hgw : ∀ᶠ n in atTop, g n w ∈ V (1/4) := by
        filter_upwards [hP (1/4) (by norm_num) le_rfl] with n hn
        exact hn w (mem_of_mem_nhds ht)
      exact key z w r hr hrU (Metric.ball_subset_closedBall hwball) hgw
  intro K hKU hK ε hε hε4
  refine hK.induction_on (p := fun s => ∀ᶠ n in atTop, ∀ x ∈ s, g n x ∈ V ε) ?_ ?_ ?_ ?_
  · simp
  · intro s t hst ht
    filter_upwards [ht] with n hn x hx using hn x (hst hx)
  · intro s t hs ht
    filter_upwards [hs, ht] with n hn1 hn2 x hx
    rcases hx with hx | hx
    exacts [hn1 x hx, hn2 x hx]
  · intro x hx
    obtain ⟨t, ht, hP⟩ := hUu (hKU hx)
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, hP ε hε hε4⟩

/-- Final step: conversion to chordal locally uniform convergence to a constant. -/
theorem aux_dsp_final (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (g : ℕ → ℂ → ℂ) (hg : ∀ n, ContinuousOn (g n) U)
    (V W : ℝ → Set ℂ)
    (hVo : ∀ ε, 0 < ε → IsOpen (V ε)) (hWo : ∀ ε, 0 < ε → IsOpen (W ε))
    (hVm : ∀ ε, 0 < ε → ε ≤ 1/4 → V ε ⊆ V (1/4))
    (hWm : ∀ ε, 0 < ε → ε ≤ 1/4 → W ε ⊆ W (1/4))
    (hdisj : Disjoint (V (1/4)) (W (1/4)))
    (hcov : ∀ K ⊆ U, IsCompact K → ∀ ε, 0 < ε → ε ≤ 1/4 →
      ∀ᶠ n in atTop, ∀ x ∈ K, g n x ∈ V ε ∪ W ε)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hgz : ∀ n, g n z₀ ∈ V (1/4))
    (c : OnePoint ℂ)
    (hc : ∀ δ > 0, ∃ ε, 0 < ε ∧ ε ≤ 1/4 ∧ ∀ w ∈ V ε, chordalDist (w : OnePoint ℂ) c < δ) :
    TendstoLocallyUniformlyOnSphere (fun n z => ((g n z : ℂ) : OnePoint ℂ)) (fun _ => c) U := by
  intro K hKU hK δ hδ
  obtain ⟨ε, hε, hε4, hεc⟩ := hc δ hδ
  filter_upwards [aux_dsp_global U hU hUc g hg V W hVo hWo hVm hWm hdisj hcov z₀ hz₀
    (Eventually.of_forall hgz) K hKU hK ε hε hε4] with n hn x hx
  exact hεc _ (hn x hx)

theorem aux_dsp_chordal_fin (w c : ℂ) :
    chordalDist (w : OnePoint ℂ) (c : OnePoint ℂ) ≤ 2 * ‖w - c‖ := by
  show 2 * ‖w - c‖ / (Real.sqrt (1 + ‖w‖ ^ 2) * Real.sqrt (1 + ‖c‖ ^ 2)) ≤ 2 * ‖w - c‖
  apply div_le_self (by positivity)
  have h1 : 1 ≤ Real.sqrt (1 + ‖w‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [norm_nonneg w])
  have h2 : 1 ≤ Real.sqrt (1 + ‖c‖ ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [norm_nonneg c])
  exact one_le_mul_of_one_le_of_one_le h1 h2

theorem aux_dsp_chordal_inf (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : R < ‖w‖) :
    chordalDist (w : OnePoint ℂ) ∞ < 2 / R := by
  show 2 / Real.sqrt (1 + ‖w‖ ^ 2) < 2 / R
  apply div_lt_div_of_pos_left (by norm_num) hR
  rw [Real.lt_sqrt hR.le]
  nlinarith

end MilnorDynamics

open MilnorDynamics

theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hdiv : DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c ∈ ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ)),
        TendstoLocallyUniformlyOnSphere (fun n z => ((f (φ n) z : ℂ) : OnePoint ℂ))
          (fun _ => c) U := by
  have hcovf : ∀ K ⊆ U, IsCompact K → ∀ ε, 0 < ε → ε ≤ 1/4 →
      ∀ᶠ n in atTop, ∀ x ∈ K,
        f n x ∈ Metric.ball 0 ε ∪ Metric.ball 1 ε ∪ (Metric.closedBall 0 ε⁻¹)ᶜ := by
    intro K hKU hK ε hε hε4
    have hK'c : IsCompact (Metric.closedBall (0:ℂ) ε⁻¹ \ (Metric.ball 0 ε ∪ Metric.ball 1 ε)) :=
      (isCompact_closedBall _ _).diff (Metric.isOpen_ball.union Metric.isOpen_ball)
    have hK'sub : Metric.closedBall (0:ℂ) ε⁻¹ \ (Metric.ball 0 ε ∪ Metric.ball 1 ε) ⊆
        ({0, 1}ᶜ : Set ℂ) := by
      rintro x ⟨-, hx⟩ hx01
      apply hx
      rcases hx01 with rfl | rfl
      · left; exact Metric.mem_ball_self hε
      · right; exact Metric.mem_ball_self hε
    filter_upwards [hdiv K hKU hK _ hK'sub hK'c] with n hn x hx
    have hnx := hn x hx
    by_contra hc
    apply hnx
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hc (Or.inr h)
    · rintro (h | h)
      · exact hc (Or.inl (Or.inl h))
      · exact hc (Or.inl (Or.inr h))
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  have hUp : IsPreconnected U := hUc.isPreconnected
  have hcont : ∀ n, ContinuousOn (f n) U := fun n => (hf n).1.continuousOn
  have hev := hcovf {z₀} (singleton_subset_iff.mpr hz₀) isCompact_singleton (1/4)
    (by norm_num) le_rfl
  have hfr : ∃ᶠ n in atTop, (f n z₀ ∈ Metric.ball (0:ℂ) (1/4) ∨
      f n z₀ ∈ Metric.ball (1:ℂ) (1/4)) ∨ f n z₀ ∈ (Metric.closedBall (0:ℂ) (1/4)⁻¹)ᶜ :=
    (hev.mono fun n hn => hn z₀ rfl).frequently
  -- general facts
  have o0 : ∀ ε, 0 < ε → IsOpen (Metric.ball (0:ℂ) ε) := fun _ _ => Metric.isOpen_ball
  have o1 : ∀ ε, 0 < ε → IsOpen (Metric.ball (1:ℂ) ε) := fun _ _ => Metric.isOpen_ball
  have oI : ∀ ε, 0 < ε → IsOpen (Metric.closedBall (0:ℂ) ε⁻¹)ᶜ :=
    fun _ _ => Metric.isClosed_closedBall.isOpen_compl
  have m0 : ∀ ε, 0 < ε → ε ≤ 1/4 → Metric.ball (0:ℂ) ε ⊆ Metric.ball 0 (1/4) :=
    fun _ _ h => Metric.ball_subset_ball h
  have m1 : ∀ ε, 0 < ε → ε ≤ 1/4 → Metric.ball (1:ℂ) ε ⊆ Metric.ball 1 (1/4) :=
    fun _ _ h => Metric.ball_subset_ball h
  have mI : ∀ ε, 0 < ε → ε ≤ 1/4 →
      (Metric.closedBall (0:ℂ) ε⁻¹)ᶜ ⊆ (Metric.closedBall (0:ℂ) (1/4)⁻¹)ᶜ :=
    fun _ hε h => compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (inv_anti₀ hε h))
  have d01 : Disjoint (Metric.ball (0:ℂ) (1/4)) (Metric.ball (1:ℂ) (1/4)) := by
    apply Metric.ball_disjoint_ball
    simp
    norm_num
  have d0I : Disjoint (Metric.ball (0:ℂ) (1/4)) (Metric.closedBall (0:ℂ) (1/4)⁻¹)ᶜ := by
    rw [Set.disjoint_compl_right_iff_subset]
    exact (Metric.ball_subset_closedBall).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have d1I : Disjoint (Metric.ball (1:ℂ) (1/4)) (Metric.closedBall (0:ℂ) (1/4)⁻¹)ᶜ := by
    rw [Set.disjoint_compl_right_iff_subset]
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have : ‖x‖ ≤ ‖x - 1‖ + ‖(1:ℂ)‖ := by
      calc ‖x‖ = ‖(x - 1) + 1‖ := by ring_nf
        _ ≤ ‖x - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
    simp at this
    norm_num
    linarith
  rcases frequently_or_distrib.mp hfr with h01 | hI
  · rcases frequently_or_distrib.mp h01 with h0 | h1
    · -- limit 0
      obtain ⟨φ, hφ, hφz⟩ := extraction_of_frequently_atTop h0
      refine ⟨φ, hφ, ((0:ℂ) : OnePoint ℂ), by simp, ?_⟩
      refine aux_dsp_final U hU hUp (fun n => f (φ n)) (fun n => hcont (φ n))
        (fun ε => Metric.ball (0:ℂ) ε)
        (fun ε => Metric.ball (1:ℂ) ε ∪ (Metric.closedBall (0:ℂ) ε⁻¹)ᶜ)
        o0 (fun ε hε => (o1 ε hε).union (oI ε hε)) m0
        (fun ε hε h => Set.union_subset_union (m1 ε hε h) (mI ε hε h))
        (Disjoint.union_right d01 d0I) ?_ z₀ hz₀ hφz _ ?_
      · intro K hKU hK ε hε hε4
        filter_upwards [hφ.tendsto_atTop.eventually (hcovf K hKU hK ε hε hε4)] with n hn x hx
        rcases hn x hx with (h | h) | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]
      · intro δ hδ
        refine ⟨min (δ / 4) (1/4), by positivity, min_le_right _ _, ?_⟩
        intro w hw
        have hw' : ‖w - 0‖ < δ / 4 := by
          have := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)
          rwa [dist_eq_norm] at this
        calc chordalDist (w : OnePoint ℂ) ((0:ℂ) : OnePoint ℂ) ≤ 2 * ‖w - 0‖ :=
              aux_dsp_chordal_fin w 0
          _ < δ := by linarith
    · -- limit 1
      obtain ⟨φ, hφ, hφz⟩ := extraction_of_frequently_atTop h1
      refine ⟨φ, hφ, ((1:ℂ) : OnePoint ℂ), by simp, ?_⟩
      refine aux_dsp_final U hU hUp (fun n => f (φ n)) (fun n => hcont (φ n))
        (fun ε => Metric.ball (1:ℂ) ε)
        (fun ε => Metric.ball (0:ℂ) ε ∪ (Metric.closedBall (0:ℂ) ε⁻¹)ᶜ)
        o1 (fun ε hε => (o0 ε hε).union (oI ε hε)) m1
        (fun ε hε h => Set.union_subset_union (m0 ε hε h) (mI ε hε h))
        (Disjoint.union_right d01.symm d1I) ?_ z₀ hz₀ hφz _ ?_
      · intro K hKU hK ε hε hε4
        filter_upwards [hφ.tendsto_atTop.eventually (hcovf K hKU hK ε hε hε4)] with n hn x hx
        rcases hn x hx with (h | h) | h
        exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
      · intro δ hδ
        refine ⟨min (δ / 4) (1/4), by positivity, min_le_right _ _, ?_⟩
        intro w hw
        have hw' : ‖w - 1‖ < δ / 4 := by
          have := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)
          rwa [dist_eq_norm] at this
        calc chordalDist (w : OnePoint ℂ) ((1:ℂ) : OnePoint ℂ) ≤ 2 * ‖w - 1‖ :=
              aux_dsp_chordal_fin w 1
          _ < δ := by linarith
  · -- limit ∞
    obtain ⟨φ, hφ, hφz⟩ := extraction_of_frequently_atTop hI
    refine ⟨φ, hφ, ∞, by simp, ?_⟩
    refine aux_dsp_final U hU hUp (fun n => f (φ n)) (fun n => hcont (φ n))
      (fun ε => (Metric.closedBall (0:ℂ) ε⁻¹)ᶜ)
      (fun ε => Metric.ball (0:ℂ) ε ∪ Metric.ball (1:ℂ) ε)
      oI (fun ε hε => (o0 ε hε).union (o1 ε hε)) mI
      (fun ε hε h => Set.union_subset_union (m0 ε hε h) (m1 ε hε h))
      (Disjoint.union_right d0I.symm d1I.symm) ?_ z₀ hz₀ hφz _ ?_
    · intro K hKU hK ε hε hε4
      filter_upwards [hφ.tendsto_atTop.eventually (hcovf K hKU hK ε hε hε4)] with n hn x hx
      rcases hn x hx with (h | h) | h
      exacts [Or.inr (Or.inl h), Or.inr (Or.inr h), Or.inl h]
    · intro δ hδ
      refine ⟨min (δ / 4) (1/4), by positivity, min_le_right _ _, ?_⟩
      intro w hw
      have hpos : 0 < min (δ / 4) (1/4) := by positivity
      have hw' : (min (δ / 4) (1/4))⁻¹ < ‖w‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw
      have hR : 0 < (min (δ / 4) (1/4))⁻¹ := inv_pos.mpr hpos
      calc chordalDist (w : OnePoint ℂ) ∞ < 2 / (min (δ / 4) (1/4))⁻¹ :=
            aux_dsp_chordal_inf w _ hR hw'
        _ = 2 * min (δ / 4) (1/4) := by rw [div_inv_eq_mul]
        _ ≤ 2 * (δ / 4) := by gcongr; exact min_le_left _ _
        _ < δ := by linarith
