-- Prove2me | solution 1 for Kyprianou.Ch02.realIntegralBindMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:43:27.281852+00:00
-- url     : https://prove2.me/submissions/09bb7da3-6ae2-4692-b6e0-8c562e4e97cf

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℝ) (hM : Measurable M)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f (P.bind M)) :
    (∀ᵐ ω ∂P, Integrable f (M ω)) ∧
      Integrable (fun ω => ∫ x, f x ∂(M ω)) P ∧
      (∫ ω, (∫ x, f x ∂(M ω)) ∂P) = ∫ x, f x ∂(P.bind M) := by
  let J : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal |f x|
  have hJ : Measurable J := ENNReal.measurable_ofReal.comp hf.abs
  have hJfin : (∫⁻ x, J x ∂(P.bind M)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (fun x => abs_nonneg (f x)))).1 hi.abs.2
  have hJL : (∫⁻ ω, ∫⁻ x, J x ∂(M ω) ∂P) < ⊤ := by
    rw [← Measure.lintegral_bind hM.aemeasurable hJ.aemeasurable]
    exact hJfin
  have hAE : ∀ᵐ ω ∂P, Integrable f (M ω) := by
    filter_upwards [ae_lt_top ((Measure.measurable_lintegral hJ).comp hM) hJL.ne] with ω h
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [Real.enorm_eq_ofReal_abs, Function.comp_def, J] using h
  have haux (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hfin : ∫⁻ x, g x ∂(P.bind M) < ⊤) :
      Integrable (fun ω => (∫⁻ x, g x ∂(M ω)).toReal) P ∧
      (∫ ω, (∫⁻ x, g x ∂(M ω)).toReal ∂P) = (∫⁻ x, g x ∂(P.bind M)).toReal := by
    let G (ω : Ω) := ∫⁻ x, g x ∂(M ω)
    have hG : Measurable G := (Measure.measurable_lintegral hg).comp hM
    have hL : (∫⁻ ω, G ω ∂P) = ∫⁻ x, g x ∂(P.bind M) :=
      (Measure.lintegral_bind hM.aemeasurable hg.aemeasurable).symm
    have hnn : ∀ᵐ ω ∂P, 0 ≤ (G ω).toReal :=
      Eventually.of_forall fun ω => ENNReal.toReal_nonneg
    have hR : (∫⁻ ω, ENNReal.ofReal (G ω).toReal ∂P) = ∫⁻ ω, G ω ∂P := by
      apply lintegral_congr_ae
      filter_upwards [ae_lt_top hG (hL.trans_ne hfin.ne)] with ω h
      exact ENNReal.ofReal_toReal h.ne
    have hm := (ENNReal.measurable_toReal.comp hG).aestronglyMeasurable (μ := P)
    constructor
    · exact ⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 (hR.trans hL ▸ hfin)⟩
    · rw [integral_eq_lintegral_of_nonneg_ae hnn hm, hR, hL]
  have hp := haux (fun x => ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp hf)
    (lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (le_abs_self _))) hJfin)
  have hn := haux (fun x => ENNReal.ofReal (-f x)) (ENNReal.measurable_ofReal.comp hf.neg)
    (lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (neg_le_abs _))) hJfin)
  have he : (fun ω => ∫ x, f x ∂(M ω)) =ᵐ[P]
      (fun ω => (∫⁻ x, ENNReal.ofReal (f x) ∂(M ω)).toReal -
        (∫⁻ x, ENNReal.ofReal (-f x) ∂(M ω)).toReal) :=
    hAE.mono fun ω h => integral_eq_lintegral_pos_part_sub_lintegral_neg_part h
  refine ⟨hAE, (hp.1.sub hn.1).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_sub hp.1 hn.1, hp.2, hn.2,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
