-- Prove2me | solution 1 for GoldieRenewal.Implicit.lemma_9_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:23:36.900235+00:00
-- url     : https://prove2.me/submissions/682b0d6d-cf55-4dd0-ad27-d752800d3f0d

import Mathlib
open MeasureTheory Filter Topology


namespace GoldieRenewal.Implicit

/-- Core of Lemma 9.3: a Tauberian argument for a nonincreasing bounded function. -/
theorem tauber_core (p : ℝ → ℝ) (hp_anti : Antitone p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (C : ℝ)
    (h : Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t, u ^ κ * p u) / t) atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => t ^ κ * p t) atTop (𝓝 C) := by
  set F : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, u ^ κ * p u with hF
  have hpm : Measurable p := hp_anti.measurable
  -- interval integrability of the integrand on any [a,b] with 0 ≤ a
  have hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → IntervalIntegrable (fun u => u ^ κ * p u) volume a b := by
    intro a b ha hab
    have h1 : IntervalIntegrable p volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine Measure.integrableOn_of_bounded (M := 1) (by simp) hpm.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 x)]; exact hp1 x
    have h2 : ContinuousOn (fun u : ℝ => u ^ κ) (Set.uIcc a b) :=
      (Real.continuous_rpow_const hκ.le).continuousOn
    have := h1.continuousOn_mul h2
    exact this
  -- the key two-sided bounds
  have hbound : ∀ l : ℝ, 1 < l → ∀ s : ℝ, 0 < s →
      s ^ κ * p (l * s) * ((l - 1) * s) ≤ F (l * s) - F s ∧
      F (l * s) - F s ≤ (l * s) ^ κ * p s * ((l - 1) * s) := by
    intro l hl s hs
    have hls : s ≤ l * s := by nlinarith
    have hdiff : F (l * s) - F s = ∫ u in s..(l * s), u ^ κ * p u :=
      intervalIntegral.integral_interval_sub_left (hII 0 (l * s) le_rfl (by nlinarith))
        (hII 0 s le_rfl hs.le)
    rw [hdiff]
    constructor
    · have := intervalIntegral.integral_mono_on (μ := volume) (a := s) (b := l * s)
        (f := fun _ => s ^ κ * p (l * s)) (g := fun u => u ^ κ * p u) hls
        intervalIntegrable_const (hII s (l * s) hs.le hls) (by
          intro x hx
          apply mul_le_mul
          · exact Real.rpow_le_rpow hs.le hx.1 hκ.le
          · exact hp_anti hx.2
          · exact hp0 _
          · exact Real.rpow_nonneg (hs.le.trans hx.1) _)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith [this]
    · have := intervalIntegral.integral_mono_on (μ := volume) (a := s) (b := l * s)
        (f := fun u => u ^ κ * p u) (g := fun _ => (l * s) ^ κ * p s) hls
        (hII s (l * s) hs.le hls) intervalIntegrable_const (by
          intro x hx
          apply mul_le_mul
          · exact Real.rpow_le_rpow (hs.le.trans hx.1) hx.2 hκ.le
          · exact hp_anti hx.1
          · exact hp0 _
          · exact Real.rpow_nonneg (by nlinarith) _)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith [this]
  -- D_l(s) := (F(ls) - F(s)) / ((l-1) s) → C
  have hD : ∀ l : ℝ, 1 < l →
      Tendsto (fun s : ℝ => (F (l * s) - F s) / ((l - 1) * s)) atTop (𝓝 C) := by
    intro l hl
    have hl0 : 0 < l := by linarith
    have hl1 : 0 < l - 1 := by linarith
    have h1 : Tendsto (fun s : ℝ => F (l * s) / (l * s)) atTop (𝓝 C) :=
      h.comp (tendsto_id.const_mul_atTop hl0)
    have h2 : Tendsto (fun s : ℝ => F s / s) atTop (𝓝 C) := h
    have h3 : Tendsto (fun s : ℝ => (l / (l - 1)) * (F (l * s) / (l * s)) - (1 / (l - 1)) * (F s / s))
        atTop (𝓝 ((l / (l - 1)) * C - (1 / (l - 1)) * C)) :=
      (h1.const_mul _).sub (h2.const_mul _)
    have heq : (l / (l - 1)) * C - (1 / (l - 1)) * C = C := by
      field_simp
    rw [heq] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    field_simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose l > 1 close to 1
  have hc1 : Tendsto (fun l : ℝ => l ^ κ * C) (𝓝[>] 1) (𝓝 ((1:ℝ) ^ κ * C)) :=
    ((Real.continuousAt_rpow_const 1 κ (Or.inl one_ne_zero)).tendsto.mono_left
      nhdsWithin_le_nhds).mul_const C
  have hc2 : Tendsto (fun l : ℝ => l ^ (-κ) * C) (𝓝[>] 1) (𝓝 ((1:ℝ) ^ (-κ) * C)) :=
    ((Real.continuousAt_rpow_const 1 (-κ) (Or.inl one_ne_zero)).tendsto.mono_left
      nhdsWithin_le_nhds).mul_const C
  rw [Real.one_rpow, one_mul] at hc1 hc2
  have hε2 : 0 < ε / 2 := by positivity
  have e1 := Metric.tendsto_nhds.1 hc1 (ε / 2) hε2
  have e2 := Metric.tendsto_nhds.1 hc2 (ε / 2) hε2
  have e3 : ∀ᶠ l in 𝓝[>] (1:ℝ), 1 < l := self_mem_nhdsWithin
  obtain ⟨l, hl1, hl2, hl⟩ := (e1.and (e2.and e3)).exists
  have hl0 : 0 < l := by linarith
  have hlκ : 0 < l ^ κ := Real.rpow_pos_of_pos hl0 _
  have hlκ' : 0 < l ^ (-κ) := Real.rpow_pos_of_pos hl0 _
  -- the two bounds as tendsto statements
  have hU : Tendsto (fun t : ℝ => l ^ κ * ((F (l * (t / l)) - F (t / l)) / ((l - 1) * (t / l))))
      atTop (𝓝 (l ^ κ * C)) :=
    ((hD l hl).comp (tendsto_id.atTop_div_const hl0)).const_mul _
  have hL : Tendsto (fun t : ℝ => l ^ (-κ) * ((F (l * t) - F t) / ((l - 1) * t)))
      atTop (𝓝 (l ^ (-κ) * C)) :=
    (hD l hl).const_mul _
  have u1 := Metric.tendsto_nhds.1 hU (ε / 2) hε2
  have u2 := Metric.tendsto_nhds.1 hL (ε / 2) hε2
  filter_upwards [u1, u2, eventually_gt_atTop 0] with t ht1 ht2 ht
  rw [Real.dist_eq] at hl1 hl2 ht1 ht2 ⊢
  rw [abs_sub_lt_iff] at hl1 hl2 ht1 ht2 ⊢
  have htl : 0 < t / l := by positivity
  have hb1 := hbound l hl (t / l) htl
  have hb2 := hbound l hl t ht
  have hlt : l * (t / l) = t := by field_simp
  rw [hlt] at hb1 ht1
  have hpos1 : 0 < (l - 1) * (t / l) := by have : 0 < l - 1 := by linarith
                                           positivity
  have hpos2 : 0 < (l - 1) * t := by have : 0 < l - 1 := by linarith
                                     positivity
  -- upper bound: t^κ p t ≤ l^κ * D(t/l)
  have hup : t ^ κ * p t ≤ l ^ κ * ((F t - F (t / l)) / ((l - 1) * (t / l))) := by
    have h1 : (t / l) ^ κ * p t ≤ (F t - F (t / l)) / ((l - 1) * (t / l)) := by
      rw [le_div_iff₀ hpos1]; exact hb1.1
    have h2 : t ^ κ = l ^ κ * (t / l) ^ κ := by
      rw [← Real.mul_rpow hl0.le htl.le, hlt]
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hlκ.le
  -- lower bound: l^{-κ} * D(t) ≤ t^κ p t
  have hlow : l ^ (-κ) * ((F (l * t) - F t) / ((l - 1) * t)) ≤ t ^ κ * p t := by
    have h1 : (F (l * t) - F t) / ((l - 1) * t) ≤ (l * t) ^ κ * p t := by
      rw [div_le_iff₀ hpos2]; exact hb2.2
    have h2 : l ^ (-κ) * (l * t) ^ κ = t ^ κ := by
      rw [Real.mul_rpow hl0.le ht.le, ← mul_assoc, ← Real.rpow_add hl0]
      simp
    calc l ^ (-κ) * ((F (l * t) - F t) / ((l - 1) * t))
        ≤ l ^ (-κ) * ((l * t) ^ κ * p t) := mul_le_mul_of_nonneg_left h1 hlκ'.le
      _ = t ^ κ * p t := by rw [← mul_assoc, h2]
  constructor <;> linarith

theorem lemma_9_3_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R) (κ : ℝ) (hκ : 0 < κ) (C : ℝ)
    (h : Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t, u ^ κ * P.real {ω | u < R ω}) / t)
      atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 C) := by
  apply tauber_core (fun u => P.real {ω | u < R ω}) _ _ _ κ hκ C h
  · intro u v huv
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω; exact lt_of_le_of_lt huv hω
  · intro u; exact measureReal_nonneg
  · intro u; exact measureReal_le_one

end GoldieRenewal.Implicit

open GoldieRenewal.Implicit


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R) (κ : ℝ) (hκ : 0 < κ) (C : ℝ)
    (h : Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t, u ^ κ * P.real {ω | u < R ω}) / t)
      atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 C) := by
  exact lemma_9_3_core P R hR κ hκ C h
