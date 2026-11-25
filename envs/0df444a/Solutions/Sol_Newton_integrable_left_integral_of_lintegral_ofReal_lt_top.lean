-- Prove2me | solution 1 for Newton.integrable_left_integral_of_lintegral_ofReal_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:05.047815+00:00
-- url     : https://prove2.me/submissions/6f60cd67-95b6-41dd-b4e8-99a47cf39aee

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
namespace Newton
theorem _root_.solution
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_aemeas : AEMeasurable H (μ.prod μ))
    (hH_int :
      ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) < ∞) :
    Integrable (fun x => ∫ y, H (x, y) ∂μ) μ := by
  -- First, upgrade to Bochner integrability of H on the product space.
  have hH_eq_ofReal_norm :
      (fun p : G × G => ENNReal.ofReal (H p)) =
        fun p => ENNReal.ofReal ‖H p‖ := by
    funext p
    have h_nonneg : 0 ≤ H p := hH_nonneg p
    have h_abs : |H p| = H p := abs_of_nonneg h_nonneg
    simp [h_abs, Real.norm_eq_abs]
  have hH_norm_int :
      ∫⁻ p, ENNReal.ofReal ‖H p‖ ∂(μ.prod μ) < ∞ := by
    simpa [hH_eq_ofReal_norm] using hH_int
  have hH_meas : AEStronglyMeasurable H (μ.prod μ) :=
    hH_aemeas.aestronglyMeasurable
  have hH_hasFinite : HasFiniteIntegral H (μ.prod μ) := by
    -- Translate the finiteness of the ofReal-lintegral into HasFiniteIntegral.
    have h_enorm_eq :
        (fun p : G × G => ‖H p‖ₑ)
          = fun p => ENNReal.ofReal ‖H p‖ := by
      funext p
      exact (ofReal_norm_eq_enorm (H p)).symm
    simpa [HasFiniteIntegral, h_enorm_eq] using hH_norm_int
  have hH_int_prod : Integrable H (μ.prod μ) :=
    ⟨hH_meas, hH_hasFinite⟩
  -- Use the product integrability to control the fibrewise integrals.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := μ)
        (f := H) hH_meas).mp hH_int_prod
  have h_section_int :
      ∀ᵐ x ∂μ, Integrable (fun y => H (x, y)) μ := by
    simpa using h_prod_info.1
  have h_majorant_int :
      Integrable (fun x => ∫ y, ‖H (x, y)‖ ∂μ) μ := by
    simpa using h_prod_info.2
  -- Measurability of the outer integral x ↦ ∫ H (x, y) dμ.
  have h_integral_meas :
      AEStronglyMeasurable (fun x => ∫ y, H (x, y) ∂μ) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := μ) (f := H) hH_meas)
  have h_norm_meas :
      AEStronglyMeasurable (fun x => ‖∫ y, H (x, y) ∂μ‖) μ :=
    h_integral_meas.norm
  -- Pointwise bound: norm of the fibrewise integral is dominated by the integral of norms.
  have h_pointwise :
      (fun x => ‖∫ y, H (x, y) ∂μ‖)
        ≤ᵐ[μ] fun x => ∫ y, ‖H (x, y)‖ ∂μ := by
    refine h_section_int.mono ?_
    intro x hx
    have hx_bound :=
      norm_integral_le_integral_norm (μ := μ) (f := fun y => H (x, y))
    simpa using hx_bound
  -- Basic integrability of the norm of the outer integral.
  have h_norm_integrable :
      Integrable (fun x => ‖∫ y, H (x, y) ∂μ‖) μ := by
    refine Integrable.mono' h_majorant_int h_norm_meas ?_
    exact h_pointwise.mono fun _ ha => by simpa using ha
  -- Package as integrability of the real-valued function x ↦ ∫ H (x, y) dμ.
  set Gfun : G → ℝ := fun x => ∫ y, H (x, y) ∂μ with hG_def
  have hG_meas : AEStronglyMeasurable Gfun μ := h_integral_meas
  have hG_hasFinite : HasFiniteIntegral Gfun μ := by
    -- From integrability of the norm of Gfun, deduce finiteness for Gfun itself.
    have h_fin_norm : HasFiniteIntegral (fun x => ‖Gfun x‖) μ :=
      h_norm_integrable.hasFiniteIntegral
    simpa [Gfun, HasFiniteIntegral] using h_fin_norm
  exact ⟨hG_meas, hG_hasFinite⟩
end Newton
