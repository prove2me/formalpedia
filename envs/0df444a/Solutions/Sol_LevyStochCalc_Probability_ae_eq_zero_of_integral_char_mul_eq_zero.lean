-- Prove2me | solution 1 for LevyStochCalc.Probability.ae_eq_zero_of_integral_char_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:53:06.255673+00:00
-- url     : https://prove2.me/submissions/ccd9229e-cfab-44b1-88fd-1f183b6b7695

import Definitions.Def_LevyStochCalc_Probability_CharTotal_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Characters separate `L¹` densities

An integrable function on an inner-product space that integrates to zero against every character
`v ↦ exp(i⟪v, w⟫)` vanishes almost everywhere. Splitting the function into positive and negative
parts turns the hypothesis into an equality of the characteristic functions of two finite
measures, which `MeasureTheory.Measure.ext_of_charFun` reads as an equality of the measures.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Probability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]

theorem AuxAZ.hint {μ : Measure V} {f : V → ℂ} (hf : Integrable f μ) (w : V) :
    Integrable (fun v => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * f v) μ := by
  refine hf.bdd_mul (c := 1) ?_ (ae_of_all _ fun v => ?_)
  · exact (by fun_prop : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)).aestronglyMeasurable
  · rw [Complex.norm_exp_ofReal_mul_I]

theorem AuxAZ.real {μ : Measure V} [IsFiniteMeasure μ] {h : V → ℝ} (hh : Integrable h μ)
    (H : ∀ w : V, ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (h v : ℂ) ∂μ = 0) :
    h =ᵐ[μ] 0 := by
  have key : ∀ f : V → ℝ, Integrable f μ → ∀ w : V,
      charFun (μ.withDensity fun v => ENNReal.ofReal (f v)) w
        = ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * ((max (f v) 0 : ℝ) : ℂ) ∂μ := by
    intro f hf w
    rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1; ext v
    rw [ENNReal.toReal_ofReal', Complex.real_smul, mul_comm]
  have hn : Integrable (fun v => -h v) μ := hh.neg
  haveI := isFiniteMeasure_withDensity_ofReal hh.2
  haveI := isFiniteMeasure_withDensity_ofReal hn.2
  have heq : μ.withDensity (fun v => ENNReal.ofReal (h v))
      = μ.withDensity (fun v => ENNReal.ofReal (-h v)) := by
    apply Measure.ext_of_charFun
    funext w
    rw [key h hh, key _ hn, ← sub_eq_zero, ← integral_sub]
    · convert H w using 2
      funext v
      have hm : max (h v) 0 - max (-h v) 0 = h v := by
        rcases le_total 0 (h v) with h1 | h1
        · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
        · rw [max_eq_right h1, max_eq_left (by linarith)]; ring
      rw [← mul_sub, ← Complex.ofReal_sub, hm]
    · exact AuxAZ.hint (hh.pos_part.ofReal (𝕜 := ℂ)) w
    · exact AuxAZ.hint (hn.pos_part.ofReal (𝕜 := ℂ)) w
  rw [withDensity_eq_iff hh.aemeasurable.ennreal_ofReal hn.aemeasurable.ennreal_ofReal
    hh.lintegral_lt_top.ne] at heq
  filter_upwards [heq] with v hv
  simp only [Pi.zero_apply]
  rcases le_total 0 (h v) with h1 | h1
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -h v ≤ 0), ENNReal.ofReal_eq_zero] at hv
    linarith
  · rw [ENNReal.ofReal_of_nonpos h1, eq_comm, ENNReal.ofReal_eq_zero] at hv
    linarith

theorem _root_.solution {μ : Measure V} [IsFiniteMeasure μ]
    {g : V → ℂ} (hg : Integrable g μ)
    (h : ∀ w : V, ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v ∂μ = 0) :
    g =ᵐ[μ] 0 := by
  have hgc : Integrable (fun v => (starRingEnd ℂ) (g v)) μ := by
    have := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hg
    simpa using this
  have hc : ∀ w : V, ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (starRingEnd ℂ) (g v) ∂μ = 0 := by
    intro w
    calc ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (starRingEnd ℂ) (g v) ∂μ
        = ∫ v, (starRingEnd ℂ) (Complex.exp ((⟪v, -w⟫ : ℝ) * Complex.I) * g v) ∂μ := by
          congr 1; ext v; rw [map_mul, char_neg, Complex.conj_conj]
      _ = (starRingEnd ℂ) (∫ v, Complex.exp ((⟪v, -w⟫ : ℝ) * Complex.I) * g v ∂μ) := integral_conj
      _ = 0 := by rw [h (-w), map_zero]
  have hre : (fun v => (g v).re) =ᵐ[μ] 0 := by
    refine AuxAZ.real hg.re fun w => ?_
    simp_rw [Complex.re_eq_add_conj, mul_div_assoc', mul_add]
    rw [integral_div, integral_add (AuxAZ.hint hg w) (AuxAZ.hint hgc w), h w, hc w]; simp
  have him : (fun v => (g v).im) =ᵐ[μ] 0 := by
    refine AuxAZ.real hg.im fun w => ?_
    simp_rw [Complex.im_eq_sub_conj, mul_div_assoc', mul_sub]
    rw [integral_div, integral_sub (AuxAZ.hint hg w) (AuxAZ.hint hgc w), h w, hc w]; simp
  filter_upwards [hre, him] with v h1 h2
  apply Complex.ext <;> simpa using by assumption

end LevyStochCalc.Probability
