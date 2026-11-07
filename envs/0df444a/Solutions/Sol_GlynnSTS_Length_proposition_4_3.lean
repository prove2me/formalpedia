-- Prove2me | solution 1 for GlynnSTS.Length.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:45:10.277+00:00
-- url     : https://prove2.me/submissions/dbd1eb84-5661-413a-aded-683b1eb55700

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting
import Theorems.Thm_GlynnSTS_Length_display_2_9

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTSProp43

noncomputable abbrev Φ : ℝ → ℝ := cdf (gaussianReal 0 1)

theorem Phi_eq_integral (y : ℝ) : Φ y = ∫ x in Set.Iic y, gaussianPDFReal 0 1 x := by
  simp only [Φ]
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic (fun x _ => gaussianPDFReal_nonneg _ _ x)

theorem Phi_eq (y : ℝ) : Φ y = Φ 0 + ∫ x in (0:ℝ)..y, gaussianPDFReal 0 1 x := by
  rw [Phi_eq_integral, Phi_eq_integral, ← intervalIntegral.integral_Iic_sub_Iic]
  · ring
  · exact (integrable_gaussianPDFReal _ _).integrableOn
  · exact (integrable_gaussianPDFReal _ _).integrableOn

theorem continuous_pdf : Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]; fun_prop

theorem hasDerivAt_Phi (y : ℝ) : HasDerivAt Φ (gaussianPDFReal 0 1 y) y := by
  have h := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := y)
    (continuous_pdf.intervalIntegrable _ _)
    (continuous_pdf.stronglyMeasurableAtFilter _ _) continuous_pdf.continuousAt
  have hfun : Φ = fun u => Φ 0 + ∫ x in (0:ℝ)..u, gaussianPDFReal 0 1 x := funext Phi_eq
  rw [hfun]
  exact h.const_add _

theorem continuous_Phi : Continuous Φ :=
  continuous_iff_continuousAt.2 (fun y => (hasDerivAt_Phi y).continuousAt)

theorem strictMono_Phi : StrictMono Φ := by
  intro a b hab
  have h1 : (gaussianReal 0 1) (Set.Ioc a b) = ENNReal.ofReal (Φ b - Φ a) := by
    simp only [Φ]
    rw [← StieltjesFunction.measure_Ioc, measure_cdf]
  have h2 : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero h0
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
    linarith
  rw [h1, Ne, ENNReal.ofReal_eq_zero, not_le] at h2
  linarith

theorem concaveOn_Phi : ConcaveOn ℝ (Set.Ici 0) Φ := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) continuous_Phi.continuousOn
    (fun x _ => (hasDerivAt_Phi x).differentiableAt.differentiableWithinAt) ?_
  rw [interior_Ici]
  intro x hx y hy hxy
  rw [(hasDerivAt_Phi x).deriv, (hasDerivAt_Phi y).deriv, gaussianPDFReal_def]
  simp only [sub_zero, NNReal.coe_one, mul_one]
  gcongr
  exact le_of_lt hx


theorem pdf_neg (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal_def, sub_zero, neg_sq]

theorem Phi_neg (x : ℝ) : Φ (-x) = 1 - Φ x := by
  let F : ℝ → ℝ := fun x => Φ (-x) + Φ x
  have hF : ∀ x, HasDerivAt F 0 x := by
    intro x
    have h1 := (hasDerivAt_Phi (-x)).comp x (hasDerivAt_neg x)
    have h2 := h1.add (hasDerivAt_Phi x)
    have h0 : gaussianPDFReal 0 1 (-x) * -1 + gaussianPDFReal 0 1 x = 0 := by
      rw [pdf_neg]; ring
    rw [h0] at h2; exact h2
  have hc : ∀ y, F y = F x := fun y =>
    is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt) (fun t => (hF t).deriv) y x
  have hlim : Tendsto F atTop (𝓝 (0 + 1)) :=
    ((tendsto_cdf_atBot (μ := gaussianReal 0 1)).comp tendsto_neg_atTop_atBot).add
      (tendsto_cdf_atTop (μ := gaussianReal 0 1))
  have hconst : Tendsto F atTop (𝓝 (F x)) := by
    have : F = fun _ => F x := funext hc
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst hlim
  simp only [F, zero_add] at this
  linarith

/-- A centered interval carries maximal standard normal mass among intervals of a given width. -/
theorem centered (a : ℝ) (ha : 0 ≤ a) (c : ℝ) :
    Φ (c + a) - Φ (c - a) ≤ Φ a - Φ (-a) := by
  let K : ℝ → ℝ := fun c => Φ (c + a) - Φ (c - a)
  have hK : ∀ c, HasDerivAt K (gaussianPDFReal 0 1 (c + a) - gaussianPDFReal 0 1 (c - a)) c := by
    intro c
    have h1 := (hasDerivAt_Phi (c + a)).comp c ((hasDerivAt_id c).add_const a)
    have h2 := (hasDerivAt_Phi (c - a)).comp c ((hasDerivAt_id c).sub_const a)
    have h := h1.sub h2
    rw [mul_one, mul_one] at h; exact h
  have hanti : AntitoneOn K (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hK t).continuousAt.continuousWithinAt)
      (fun t _ => (hK t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht' : 0 < t := ht
    rw [(hK t).deriv, sub_nonpos, gaussianPDFReal_def]
    simp only [sub_zero, NNReal.coe_one, mul_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    have : (t - a) ^ 2 ≤ (t + a) ^ 2 := by nlinarith
    linarith
  have hsym : ∀ c, K (-c) = K c := by
    intro c
    simp only [K]
    rw [show -c + a = -(c - a) by ring, show -c - a = -(c + a) by ring, Phi_neg, Phi_neg]
    ring
  have h0 : K 0 = Φ a - Φ (-a) := by simp only [K, zero_add, zero_sub]
  rcases le_total 0 c with hc | hc
  · have := hanti (Set.mem_Ici.2 le_rfl) hc hc
    simp only [K] at this h0 ⊢
    linarith
  · have := hanti (Set.mem_Ici.2 le_rfl) (show (0:ℝ) ≤ -c by linarith) (by linarith)
    rw [hsym c] at this
    simp only [K] at this h0 ⊢
    linarith

end GlynnSTSProp43

open GlynnSTSProp43 in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : ℝ) (hz : GlynnSTS.Length.H P B g z = 1 - δ / 2) :
    GlynnSTS.Length.H P B g z - GlynnSTS.Length.H P B g (-z) = 1 - δ ∧
      ∀ α β : ℝ, GlynnSTS.Length.H P B g β - GlynnSTS.Length.H P B g α = 1 - δ →
        2 * z ≤ β - α := by
  have h29 := GlynnSTS.Length.display_2_9 P B hB g hg
  have hmeas : AEMeasurable (fun ω => g (B ω)) P := (hg.1.comp hB.1).aemeasurable
  set G := P.map (fun ω => g (B ω)) with hGdef
  haveI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map hmeas
  have hpos : ∀ᵐ y ∂G, y ∈ Set.Ioi (0 : ℝ) :=
    (ae_map_iff hmeas measurableSet_Ioi).2 hg.2.2.2.1
  have hres : G.restrict (Set.Ioi 0) = G := Measure.restrict_eq_self_of_ae_mem hpos
  have hH : ∀ x, GlynnSTS.Length.H P B g x = ∫ y, Φ (x * y) ∂G := by
    intro x; rw [h29 x, hres]
  have hI : ∀ x, Integrable (fun y => Φ (x * y)) G := by
    intro x
    refine Integrable.of_bound (C := 1)
      (continuous_Phi.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall (fun y => ?_))
    try simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [cdf_nonneg (gaussianReal 0 1) (x * y)], cdf_le_one _ _⟩
  have hneg : ∀ x, GlynnSTS.Length.H P B g (-x) = 1 - GlynnSTS.Length.H P B g x := by
    intro x
    rw [hH, hH]
    have : (fun y => Φ (-x * y)) = fun y => 1 - Φ (x * y) := by
      funext y; rw [neg_mul, Phi_neg]
    rw [this, integral_sub (integrable_const _) (hI x), integral_const, probReal_univ,
      one_smul]
  have hmono : ∀ x x', x ≤ x' → GlynnSTS.Length.H P B g x ≤ GlynnSTS.Length.H P B g x' := by
    intro x x' hxx
    rw [hH, hH]
    refine integral_mono_ae (hI x) (hI x') ?_
    filter_upwards [hpos] with y hy
    exact strictMono_Phi.monotone (mul_le_mul_of_nonneg_right hxx (le_of_lt hy))
  have hstrict : ∀ x x', x < x' → GlynnSTS.Length.H P B g x < GlynnSTS.Length.H P B g x' := by
    intro x x' hxx
    refine lt_of_le_of_ne (hmono x x' hxx.le) (fun heq => ?_)
    have hnn : 0 ≤ᵐ[G] fun y => Φ (x' * y) - Φ (x * y) := by
      filter_upwards [hpos] with y hy
      exact sub_nonneg.2 (strictMono_Phi.monotone (mul_le_mul_of_nonneg_right hxx.le (le_of_lt hy)))
    have h0 : ∫ y, (Φ (x' * y) - Φ (x * y)) ∂G = 0 := by
      rw [integral_sub (hI x') (hI x), ← hH, ← hH, heq, sub_self]
    have hz0 := (integral_eq_zero_iff_of_nonneg_ae hnn ((hI x').sub (hI x))).1 h0
    have hfalse : ∀ᵐ y ∂G, False := by
      filter_upwards [hz0, hpos] with y hy hyp
      have : Φ (x * y) < Φ (x' * y) := strictMono_Phi (mul_lt_mul_of_pos_right hxx hyp)
      simp only [Pi.zero_apply] at hy
      linarith
    rw [eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
    exact IsProbabilityMeasure.ne_zero G hfalse
  refine ⟨by rw [hneg, hz]; ring, ?_⟩
  intro α β hαβ
  by_contra hlt
  rw [not_le] at hlt
  set c := (α + β) / 2 with hc
  set w := (β - α) / 2 with hw
  rcases le_or_gt w 0 with hw0 | hw0
  · have := hmono β α (by linarith)
    linarith
  have hβ : β = c + w := by rw [hc, hw]; ring
  have hα : α = c - w := by rw [hc, hw]; ring
  have hle : GlynnSTS.Length.H P B g β - GlynnSTS.Length.H P B g α ≤
      GlynnSTS.Length.H P B g w - GlynnSTS.Length.H P B g (-w) := by
    rw [hH, hH, hH, hH, ← integral_sub (hI _) (hI _), ← integral_sub (hI _) (hI _)]
    refine integral_mono_ae ((hI _).sub (hI _)) ((hI _).sub (hI _)) ?_
    filter_upwards [hpos] with y hy
    have := centered (w * y) (mul_nonneg hw0.le (le_of_lt hy)) (c * y)
    rw [hβ, hα, add_mul, sub_mul, neg_mul]
    exact this
  have hwz : GlynnSTS.Length.H P B g w < GlynnSTS.Length.H P B g z := hstrict w z (by linarith)
  rw [hneg] at hle
  linarith
