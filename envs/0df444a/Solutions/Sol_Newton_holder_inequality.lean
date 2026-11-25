-- Prove2me | solution 1 for Newton.holder_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:45.618803+00:00
-- url     : https://prove2.me/submissions/ebf014f9-0b3e-44e0-b79e-4431665ba933

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Theorems.Thm_Newton_holder_inequality_one_infty

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Newton
theorem _root_.solution
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → E) (g : α → F)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) μ ∧
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  rcases hpq with hpq | hpq | hpq
  · rcases hpq with ⟨hp, hq⟩
    subst hp; subst hq
    -- Case `p = 1`, `q = ∞`
    have hf_int : Integrable f μ := by
      simpa [memLp_one_iff_integrable] using hf
    obtain ⟨hg_meas, hg_fin⟩ := hg
    have hg_bound : ∃ C, ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
      have hg_ne_top' : eLpNorm g ∞ μ ≠ ∞ := ne_of_lt hg_fin
      have hg_ne_top : eLpNormEssSup g μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hg_ne_top'
      refine ⟨(eLpNorm g ∞ μ).toReal, ?_⟩
      refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => g x)).mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖g x‖ ≤ eLpNormEssSup g μ := by
        simpa [ofReal_norm_eq_enorm] using hx
      have := (ENNReal.ofReal_le_iff_le_toReal hg_ne_top).mp hx'
      simpa [eLpNorm, eLpNorm_exponent_top] using this
    have hg_ae : AEStronglyMeasurable g μ := hg_meas
    have :=
      holder_inequality_one_infty (μ := μ) (f := f) (g := g) hf_int hg_ae hg_bound
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hg_bound
      set C₀ := max C 0
      have hC₀_nonneg : 0 ≤ C₀ := le_max_right _ _
      have hC₀_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C₀ :=
        hC.mono fun x hx => le_max_of_le_left hx
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_int.aestronglyMeasurable.norm.mul hg_ae.norm)
      have h_dom : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C₀ * ‖f x‖ :=
        hC₀_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg : 0 ≤ ‖g x‖ := norm_nonneg _
            have hmul_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hf_nonneg hg_nonneg
            have h_rhs_nonneg : 0 ≤ C₀ * ‖f x‖ := mul_nonneg hC₀_nonneg hf_nonneg
            have hmul_le : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C₀ :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg : _)
            simpa [Real.norm_of_nonneg hmul_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using hmul_le
      have h_majorant : Integrable (fun x => C₀ * ‖f x‖) μ :=
        (hf_int.norm.const_mul C₀)
      exact Integrable.mono' h_majorant h_meas h_dom
    · -- Express the L¹ norm of `f` via `eLpNorm`.
      have hf_norm : Integrable (fun x => ‖f x‖) μ := hf_int.norm
      have hf_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
        Filter.Eventually.of_forall fun _ => norm_nonneg _
      have hf_lintegral :
          ∫⁻ x, ENNReal.ofReal (‖f x‖) ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_norm hf_nonneg).symm
      have hf_eLpNorm :
          eLpNorm f 1 μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm]
          using hf_lintegral
      have hf_toReal :
          (eLpNorm f 1 μ).toReal = ∫ x, ‖f x‖ ∂μ := by
        have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ∂μ :=
          integral_nonneg fun _ => norm_nonneg _
        have := congrArg ENNReal.toReal hf_eLpNorm
        simpa [h_nonneg, ENNReal.toReal_ofReal] using this
      -- Obtain the essential supremum bound for `g` with the precise constant.
      have hg_ne_top' : eLpNorm g ∞ μ ≠ ∞ := ne_of_lt hg_fin
      have hg_ne_top : eLpNormEssSup g μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hg_ne_top'
      set K := (eLpNorm g ∞ μ).toReal with hK
      have hK_nonneg : 0 ≤ K := by
        simp [K]
      have hK_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ K := by
        refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => g x)).mono ?_
        intro x hx
        have hx' : ENNReal.ofReal ‖g x‖ ≤ eLpNormEssSup g μ := by
          simpa [ofReal_norm_eq_enorm] using hx
        have := (ENNReal.ofReal_le_iff_le_toReal hg_ne_top).mp hx'
        simpa [K, eLpNorm, eLpNorm_exponent_top] using this
      -- Compare the product with the majorant `K * ‖f x‖`.
      have hf_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_int.aestronglyMeasurable.norm.mul hg_ae.norm)
      have h_mul_le :
          (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => K * ‖f x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg' : 0 ≤ ‖f x‖ := norm_nonneg _
            have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * K :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg' : _)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_mul_abs :
          ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ K * ‖f x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg' : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ :=
              mul_nonneg hf_nonneg' hg_nonneg'
            have h_rhs_nonneg : 0 ≤ K * ‖f x‖ := mul_nonneg hK_nonneg hf_nonneg'
            have : ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * K :=
              (mul_le_mul_of_nonneg_left hx hf_nonneg' : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using this
      have h_majorant : Integrable (fun x => K * ‖f x‖) μ :=
        hf_norm.const_mul K
      have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
        Integrable.mono' h_majorant hf_meas h_mul_abs
      have h_integral_le :=
        integral_mono_ae h_prod_int h_majorant h_mul_le
      have h_integral_const :
          ∫ x, K * ‖f x‖ ∂μ = K * ∫ x, ‖f x‖ ∂μ := by
        simpa [mul_comm] using
          integral_const_mul (μ := μ) (r := K) (f := fun x => ‖f x‖)
      have h_main :
          ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ K * ∫ x, ‖f x‖ ∂μ := by
        simpa [h_integral_const] using h_integral_le
      simpa [hf_toReal, K, mul_comm, mul_left_comm, mul_assoc] using h_main
  · rcases hpq with ⟨hp, hq⟩
    subst hp; subst hq
    -- Case `p = ∞`, `q = 1`
    have hg_int : Integrable g μ := by
      simpa [memLp_one_iff_integrable] using hg
    obtain ⟨hf_meas, hf_fin⟩ := hf
    have hf_bound : ∃ C, ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
      have hf_ne_top' : eLpNorm f ∞ μ ≠ ∞ := ne_of_lt hf_fin
      have hf_ne_top : eLpNormEssSup f μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hf_ne_top'
      refine ⟨(eLpNorm f ∞ μ).toReal, ?_⟩
      refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => f x)).mono ?_
      intro x hx
      have hx' : ENNReal.ofReal ‖f x‖ ≤ eLpNormEssSup f μ := by
        simpa [ofReal_norm_eq_enorm] using hx
      have := (ENNReal.ofReal_le_iff_le_toReal hf_ne_top).mp hx'
      simpa [eLpNorm, eLpNorm_exponent_top] using this
    have hf_ae : AEStronglyMeasurable f μ := hf_meas
    have := by
      have h :=
        holder_inequality_one_infty (μ := μ) (E := F) (F := E)
          (f := g) (g := f) hg_int hf_ae hf_bound
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hf_bound
      set C₀ := max C 0
      have hC₀_nonneg : 0 ≤ C₀ := le_max_right _ _
      have hC₀_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C₀ :=
        hC.mono fun x hx => le_max_of_le_left hx
      have hg_meas : AEStronglyMeasurable g μ := hg_int.aestronglyMeasurable
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_ae.norm.mul hg_meas.norm)
      have h_dom : ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ C₀ * ‖g x‖ :=
        hC₀_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ := mul_nonneg hf_nonneg hg_nonneg
            have h_rhs_nonneg : 0 ≤ C₀ * ‖g x‖ := mul_nonneg hC₀_nonneg hg_nonneg
            have h_mul_le : ‖f x‖ * ‖g x‖ ≤ C₀ * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using h_mul_le
      have h_majorant : Integrable (fun x => C₀ * ‖g x‖) μ :=
        hg_int.norm.const_mul C₀
      exact Integrable.mono' h_majorant h_meas h_dom
    · -- Express the L¹ norm of `g` via `eLpNorm`.
      have hg_norm : Integrable (fun x => ‖g x‖) μ := hg_int.norm
      have hg_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ :=
        Filter.Eventually.of_forall fun _ => norm_nonneg _
      have hg_lintegral :
          ∫⁻ x, ENNReal.ofReal (‖g x‖) ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ∂μ) := by
        simpa using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_norm hg_nonneg).symm
      have hg_eLpNorm :
          eLpNorm g 1 μ = ENNReal.ofReal (∫ x, ‖g x‖ ∂μ) := by
        simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm]
          using hg_lintegral
      have hg_toReal :
          (eLpNorm g 1 μ).toReal = ∫ x, ‖g x‖ ∂μ := by
        have h_nonneg : 0 ≤ ∫ x, ‖g x‖ ∂μ :=
          integral_nonneg fun _ => norm_nonneg _
        have := congrArg ENNReal.toReal hg_eLpNorm
        simpa [h_nonneg, ENNReal.toReal_ofReal] using this
      -- Obtain the essential supremum bound for `f` with the precise constant.
      have hf_ne_top' : eLpNorm f ∞ μ ≠ ∞ := ne_of_lt hf_fin
      have hf_ne_top : eLpNormEssSup f μ ≠ ∞ :=
        by simpa [eLpNorm, eLpNorm_exponent_top] using hf_ne_top'
      set K := (eLpNorm f ∞ μ).toReal with hK
      have hK_nonneg : 0 ≤ K := by
        simp [K]
      have hK_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ K := by
        refine (ae_le_eLpNormEssSup (μ := μ) (f := fun x => f x)).mono ?_
        intro x hx
        have hx' : ENNReal.ofReal ‖f x‖ ≤ eLpNormEssSup f μ := by
          simpa [ofReal_norm_eq_enorm] using hx
        have := (ENNReal.ofReal_le_iff_le_toReal hf_ne_top).mp hx'
        simpa [K, eLpNorm, eLpNorm_exponent_top] using this
      -- Compare the product with the majorant `K * ‖g x‖`.
      have hg_meas : AEStronglyMeasurable g μ := hg_int.aestronglyMeasurable
      have h_meas : AEStronglyMeasurable (fun x => ‖f x‖ * ‖g x‖) μ :=
        (hf_ae.norm.mul hg_meas.norm)
      have h_mul_le :
          (fun x => ‖f x‖ * ‖g x‖) ≤ᵐ[μ] fun x => K * ‖g x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have : ‖f x‖ * ‖g x‖ ≤ K * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg' : _)
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h_mul_abs :
          ∀ᵐ x ∂μ, ‖‖f x‖ * ‖g x‖‖ ≤ K * ‖g x‖ :=
        hK_bound.mono fun x hx =>
          by
            have hf_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
            have hg_nonneg' : 0 ≤ ‖g x‖ := norm_nonneg _
            have h_prod_nonneg : 0 ≤ ‖f x‖ * ‖g x‖ :=
              mul_nonneg hf_nonneg hg_nonneg'
            have h_rhs_nonneg : 0 ≤ K * ‖g x‖ :=
              mul_nonneg hK_nonneg hg_nonneg'
            have : ‖f x‖ * ‖g x‖ ≤ K * ‖g x‖ :=
              (mul_le_mul_of_nonneg_right hx hg_nonneg' : _)
            simpa [Real.norm_of_nonneg h_prod_nonneg, Real.norm_of_nonneg h_rhs_nonneg,
              mul_comm, mul_left_comm, mul_assoc] using this
      have h_majorant : Integrable (fun x => K * ‖g x‖) μ :=
        hg_norm.const_mul K
      have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
        Integrable.mono' h_majorant h_meas h_mul_abs
      have h_integral_le :=
        integral_mono_ae h_prod_int h_majorant h_mul_le
      have h_integral_const :
          ∫ x, K * ‖g x‖ ∂μ = K * ∫ x, ‖g x‖ ∂μ := by
        simpa [mul_comm] using
          integral_const_mul (μ := μ) (r := K) (f := fun x => ‖g x‖)
      have h_main :
          ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤ K * ∫ x, ‖g x‖ ∂μ := by
        simpa [h_integral_const] using h_integral_le
      simpa [hg_toReal, K, mul_comm, mul_left_comm, mul_assoc] using h_main
  · rcases hpq with ⟨hp, hp_top, hq, hq_top, hpq'⟩
    -- Case `1 < p, q < ∞`
    set pr := p.toReal with hpr
    set qr := q.toReal with hqr
    have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
    have hq_ne_top : q ≠ ∞ := ne_of_lt hq_top
    have hp_pos : 0 < p :=
      lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ 1 by simp) hp
    have hq_pos : 0 < q :=
      lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ 1 by simp) hq
    have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
    have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
    have hp_real_gt_one : 1 < pr := by
      have h₁ : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_lt_toReal h₁ hp_ne_top).2 hp
      simpa [hpr] using this
    have hq_real_gt_one : 1 < qr := by
      have h₁ : (1 : ℝ≥0∞) ≠ ∞ := by simp
      have := (ENNReal.toReal_lt_toReal h₁ hq_ne_top).2 hq
      simpa [hqr] using this
    have pr_pos : 0 < pr := zero_lt_one.trans hp_real_gt_one
    have qr_pos : 0 < qr := zero_lt_one.trans hq_real_gt_one
    have pr_nonneg : 0 ≤ pr := pr_pos.le
    have qr_nonneg : 0 ≤ qr := qr_pos.le
    have hp_inv_ne_top : 1 / p ≠ ∞ := by
      simpa [one_div] using (ENNReal.inv_ne_top).2 hp_ne_zero
    have hq_inv_ne_top : 1 / q ≠ ∞ := by
      simpa [one_div] using (ENNReal.inv_ne_top).2 hq_ne_zero
    have hp_inv_toReal : (1 / p).toReal = 1 / pr := by
      simp [one_div, hpr, ENNReal.toReal_inv]
    have hq_inv_toReal : (1 / q).toReal = 1 / qr := by
      simp [one_div, hqr, ENNReal.toReal_inv]
    have hpq_real_sum : 1 / pr + 1 / qr = 1 := by
      have h := congrArg ENNReal.toReal hpq'
      have hsum_symm : (1 / p).toReal + (1 / q).toReal = (1 / p + 1 / q).toReal :=
        (ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top).symm
      have h_toReal_add : (1 / p).toReal + (1 / q).toReal = 1 :=
        hsum_symm.trans h
      simpa [hp_inv_toReal, hq_inv_toReal] using h_toReal_add
    have hpq_real_sum' : pr⁻¹ + qr⁻¹ = 1 := by
      simpa [one_div] using hpq_real_sum
    have hpq_real : pr.HolderConjugate qr :=
      (Real.holderConjugate_iff).2 ⟨hp_real_gt_one, hpq_real_sum'⟩
    have hp_ofReal : ENNReal.ofReal pr = p := by
      simp [hpr, hp_ne_top]
    have hq_ofReal : ENNReal.ofReal qr = q := by
      simp [hqr, hq_ne_top]
    have hf_norm : MemLp (fun x => ‖f x‖) p μ := hf.norm
    have hg_norm : MemLp (fun x => ‖g x‖) q μ := hg.norm
    have hf_norm_real : MemLp (fun x => ‖f x‖) (ENNReal.ofReal pr) μ := by
      simpa [hp_ofReal] using hf_norm
    have hg_norm_real : MemLp (fun x => ‖g x‖) (ENNReal.ofReal qr) μ := by
      simpa [hq_ofReal] using hg_norm
    have hf_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hg_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    have hf_pow_integrable : Integrable (fun x => ‖f x‖ ^ pr) μ :=
      hf.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hg_pow_integrable : Integrable (fun x => ‖g x‖ ^ qr) μ :=
      hg.integrable_norm_rpow hq_ne_zero hq_ne_top
    have hf_pow_nonneg : 0 ≤ᵐ[μ] fun x => ‖f x‖ ^ pr :=
      Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hg_pow_nonneg : 0 ≤ᵐ[μ] fun x => ‖g x‖ ^ qr :=
      Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
    haveI : ENNReal.HolderConjugate p q :=
      ⟨by simpa [one_div] using hpq'⟩
    have h_prod_int : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
      MemLp.integrable_mul (p := p) (q := q) hf_norm hg_norm
    have hf_lintegral :
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ pr) ∂μ =
            ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_pow_integrable
            hf_pow_nonneg).symm
    have hg_lintegral :
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ qr) ∂μ =
            ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_pow_integrable
            hg_pow_nonneg).symm
    have hf_integral_eq :
        ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      have h :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_pow_integrable
            hf_pow_nonneg).symm
      have hfun :
          (fun x => ENNReal.ofReal (‖f x‖ ^ pr)) = fun x => ‖f x‖ₑ ^ pr := by
        funext x
        simpa [ofReal_norm_eq_enorm]
          using (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) pr_nonneg).symm
      simpa [hfun] using h
    have hg_integral_eq :
        ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      have h :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_pow_integrable
            hg_pow_nonneg).symm
      have hfun :
          (fun x => ENNReal.ofReal (‖g x‖ ^ qr)) = fun x => ‖g x‖ₑ ^ qr := by
        funext x
        simpa [ofReal_norm_eq_enorm]
          using (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) qr_nonneg).symm
      simpa [hfun] using h
    set Af := ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ with hAf
    set Ag := ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ with hAg
    have hAf_eq : Af = ENNReal.ofReal (∫ x, ‖f x‖ ^ pr ∂μ) := by
      simpa [hAf] using hf_integral_eq
    have hAg_eq : Ag = ENNReal.ofReal (∫ x, ‖g x‖ ^ qr ∂μ) := by
      simpa [hAg] using hg_integral_eq
    have hAf_ne_top : Af ≠ ∞ := by
      simp [hAf_eq]
    have hAg_ne_top : Ag ≠ ∞ := by
      simp [hAg_eq]
    have hf_integral_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ pr ∂μ :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hAf_toReal : Af.toReal = ∫ x, ‖f x‖ ^ pr ∂μ := by
      have := congrArg ENNReal.toReal hAf_eq
      simpa [hf_integral_nonneg, ENNReal.toReal_ofReal] using this
    have hg_integral_nonneg : 0 ≤ ∫ x, ‖g x‖ ^ qr ∂μ :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hAg_toReal : Ag.toReal = ∫ x, ‖g x‖ ^ qr ∂μ := by
      have := congrArg ENNReal.toReal hAg_eq
      simpa [hg_integral_nonneg, ENNReal.toReal_ofReal] using this
    have hf_norm_rpow : (∫ x, ‖f x‖ ^ pr ∂μ) ^ (1 / pr) =
        (eLpNorm f p μ).toReal := by
      have hf_eLpNorm :=
        eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := f) hp_ne_zero hp_ne_top
      have h := congrArg ENNReal.toReal hf_eLpNorm
      have h_power : (Af ^ (1 / pr)).toReal = Af.toReal ^ (1 / pr) := by
        simpa using (ENNReal.toReal_rpow Af (1 / pr)).symm
      have h_main : (Af ^ (1 / pr)).toReal = (eLpNorm f p μ).toReal := by
        simpa [hAf] using h.symm
      have h_lhs : (Af ^ (1 / pr)).toReal =
          (∫ x, ‖f x‖ ^ pr ∂μ) ^ (1 / pr) := by
        simpa [hAf_toReal] using h_power
      exact h_lhs.symm.trans h_main
    have hg_norm_rpow : (∫ x, ‖g x‖ ^ qr ∂μ) ^ (1 / qr) =
        (eLpNorm g q μ).toReal := by
      have hg_eLpNorm :=
        eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := g) hq_ne_zero hq_ne_top
      have h := congrArg ENNReal.toReal hg_eLpNorm
      have h_power : (Ag ^ (1 / qr)).toReal = Ag.toReal ^ (1 / qr) := by
        simpa using (ENNReal.toReal_rpow Ag (1 / qr)).symm
      have h_main : (Ag ^ (1 / qr)).toReal = (eLpNorm g q μ).toReal := by
        simpa [hAg] using h.symm
      have h_lhs : (Ag ^ (1 / qr)).toReal =
          (∫ x, ‖g x‖ ^ qr ∂μ) ^ (1 / qr) := by
        simpa [hAg_toReal] using h_power
      exact h_lhs.symm.trans h_main
    have hf_norm_rpow_inv : (∫ x, ‖f x‖ ^ pr ∂μ) ^ pr⁻¹ =
        (eLpNorm f p μ).toReal := by
      simpa [one_div] using hf_norm_rpow
    have hg_norm_rpow_inv : (∫ x, ‖g x‖ ^ qr ∂μ) ^ qr⁻¹ =
        (eLpNorm g q μ).toReal := by
      simpa [one_div] using hg_norm_rpow
    have h_main :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := pr) (q := qr)
        hpq_real hf_nonneg hg_nonneg hf_norm_real hg_norm_real
    have h_final :
        ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
          (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
      simpa [hf_norm_rpow_inv, hg_norm_rpow_inv] using h_main
    exact ⟨h_prod_int, h_final⟩
end Newton
