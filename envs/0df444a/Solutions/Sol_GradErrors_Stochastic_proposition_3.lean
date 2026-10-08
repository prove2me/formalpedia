-- Prove2me | solution 1 for GradErrors.Stochastic.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:20:30.152741+00:00
-- url     : https://prove2.me/submissions/97b4b95a-3259-4380-a6f0-4b2ae8f611aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GradErrors_Stochastic_lemma_6

set_option autoImplicit false
open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

namespace D5G

theorem prop3_det {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (h1 : Tendsto (fun t => f (x t)) atTop atBot ∨ ∃ l : ℝ, Tendsto (fun t => f (x t)) atTop (𝓝 l))
    (h2 : ∀ k : ℕ, (¬ Tendsto (fun t => f (x t)) atTop atBot →
      ∀ δ' > 1 / ((k : ℝ) + 1), ∀ᶠ t in atTop, ‖gradient f (x t)‖ ≤ δ')) :
    (Tendsto (fun t => f (x t)) atTop atBot ∨
      ((∃ l : ℝ, Tendsto (fun t => f (x t)) atTop (𝓝 l)) ∧
        Tendsto (fun t => gradient f (x t)) atTop (𝓝 0))) ∧
    ∀ xbar, MapClusterPt xbar atTop x → gradient f xbar = 0 := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous (gradient f) := hL.continuous
  by_cases hb : Tendsto (fun t => f (x t)) atTop atBot
  · refine ⟨Or.inl hb, fun xbar hcl => ?_⟩
    exfalso
    have hU : f ⁻¹' Set.Ioo (f xbar - 1) (f xbar + 1) ∈ 𝓝 xbar :=
      hfc.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
    have hfr := (mapClusterPt_iff_frequently.1 hcl) _ hU
    have hev := (tendsto_atBot.1 hb) (f xbar - 2)
    obtain ⟨t, ht1, ht2⟩ := (hfr.and_eventually hev).exists
    have := ht1.1
    linarith
  · have hg0 : Tendsto (fun t => gradient f (x t)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall (fun t => lt_of_lt_of_le ha (norm_nonneg _)),
        fun a ha => ?_⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos ha)
      filter_upwards [h2 k hb (a / 2) hk] with t ht
      linarith
    refine ⟨Or.inr ⟨h1.resolve_left hb, hg0⟩, fun xbar hcl => ?_⟩
    by_contra hne
    have hpos : 0 < ‖gradient f xbar‖ := norm_pos_iff.2 hne
    have hU : (fun y => gradient f y) ⁻¹' Metric.ball (gradient f xbar) (‖gradient f xbar‖ / 2) ∈ 𝓝 xbar :=
      hgc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hpos))
    have hfr := (mapClusterPt_iff_frequently.1 hcl) _ hU
    have hev : ∀ᶠ t in atTop, ‖gradient f (x t)‖ < ‖gradient f xbar‖ / 2 := by
      have := (tendsto_zero_iff_norm_tendsto_zero.1 hg0)
      exact (tendsto_order.1 this).2 _ (half_pos hpos)
    obtain ⟨t, ht1, ht2⟩ := (hfr.and_eventually hev).exists
    have h3 : ‖gradient f (x t) - gradient f xbar‖ < ‖gradient f xbar‖ / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using ht1
    have h4 := norm_sub_norm_le (gradient f xbar) (gradient f (x t))
    rw [norm_sub_rev] at h4
    linarith

end D5G

theorem solution {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t)
    (hx : ∀ t ω, x (t + 1) ω = x t ω + γ t • (s t ω + w t ω))
    (hxm : ∀ t, StronglyMeasurable[ℱ t] (x t)) (hsm : ∀ t, StronglyMeasurable[ℱ t] (s t))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : ∀ t ω, c₁ * ‖gradient f (x t ω)‖ ^ 2 ≤ -⟪gradient f (x t ω), s t ω⟫_ℝ)
    (h41b : ∀ t ω, ‖s t ω‖ ≤ c₂ * (1 + ‖gradient f (x t ω)‖))
    (A : ℝ) (hA : 0 < A)
    (h42 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S → ∫⁻ ω in S, ‖w t ω‖ₑ ∂P < ∞ →
      ∫ ω in S, w t ω ∂P = 0)
    (h43 : ∀ t (S : Set Ω), MeasurableSet[ℱ t] S →
      ∫⁻ ω in S, ‖w t ω‖ₑ ^ 2 ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (A * (1 + ‖gradient f (x t ω)‖ ^ 2)) ∂P)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ∀ᵐ ω ∂P,
      (Tendsto (fun t => f (x t ω)) atTop atBot ∨
        ((∃ l : ℝ, Tendsto (fun t => f (x t ω)) atTop (𝓝 l)) ∧
          Tendsto (fun t => gradient f (x t ω)) atTop (𝓝 0))) ∧
      ∀ xbar, MapClusterPt xbar atTop (fun t => x t ω) → gradient f xbar = 0 := by
  have hall := ae_all_iff.2 (fun k : ℕ =>
    GradErrors.Stochastic.lemma_6 P ℱ f hf L hL x s w γ hγ hx hxm hsm c₁ c₂ hc₁ hc₂ h41a h41b A hA
      h42 h43 hsum hsq (1 / ((k : ℝ) + 1)) (by positivity))
  filter_upwards [hall] with ω hω
  exact D5G.prop3_det f hf L hL (fun t => x t ω) (hω 0).1 (fun k => (hω k).2)
