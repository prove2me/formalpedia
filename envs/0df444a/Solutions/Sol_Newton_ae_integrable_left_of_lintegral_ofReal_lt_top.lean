-- Prove2me | solution 1 for Newton.ae_integrable_left_of_lintegral_ofReal_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:06:59.964549+00:00
-- url     : https://prove2.me/submissions/5db885af-f15b-430d-81b1-918d0634f432

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Theorems.Thm_Newton_tonelli_ae_section_lt_top_of_aemeasurable_left

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
    ∀ᵐ x ∂μ, Integrable (fun y => H (x, y)) μ := by
  -- Apply the ℝ≥0∞-valued Tonelli consequence to the kernel `ofReal ∘ H`.
  have hH_ofReal_aemeas :
      AEMeasurable (fun p : G × G => ENNReal.ofReal (H p)) (μ.prod μ) :=
    hH_aemeas.ennreal_ofReal
  have h_section_lt_top :
      ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (H (x, y)) ∂μ < ∞ :=
    tonelli_ae_section_lt_top_of_aemeasurable_left
      (μ := μ) (f := fun p : G × G => ENNReal.ofReal (H p))
      hH_ofReal_aemeas hH_int
  -- a.e. strong measurability of the sections x ↦ H (x, ·).
  have h_section_aesm :
      ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => H (x, y)) μ := by
    -- Extract a measurable representative H' of H on μ.prod μ.
    rcases hH_aemeas with ⟨H', hH'_meas, hH_eq⟩
    -- From H = H' a.e. on μ.prod μ, deduce a.e. equality on almost every fibre.
    have h_section_ae :
        ∀ᵐ x ∂μ, (fun y => H' (x, y)) =ᵐ[μ] fun y => H (x, y) := by
      have h_curry :
          ∀ᵐ x ∂μ, (fun y => H (x, y)) =ᵐ[μ] fun y => H' (x, y) :=
        Measure.ae_ae_eq_curry_of_prod (μ := μ) (ν := μ) hH_eq
      refine h_curry.mono ?_
      intro x hx
      simpa using hx.symm
    -- Sections of the measurable representative are measurable.
    have hH'_section_meas :
        ∀ x, Measurable fun y => H' (x, y) := fun x =>
      hH'_meas.comp (measurable_const.prodMk measurable_id)
    -- Package measurability and a.e. equality into AEStronglyMeasurable for H(x, ·).
    refine h_section_ae.mono ?_
    intro x hx
    exact (hH'_section_meas x).aestronglyMeasurable.congr hx
  -- From finiteness of the `ofReal` lintegral and nonnegativity,
  -- deduce Bochner integrability of the real-valued sections.
  refine (h_section_lt_top.and h_section_aesm).mono ?_
  intro x hx
  rcases hx with ⟨hx, hx_aesm⟩
  -- Rewrite the integrand using `‖H (x, y)‖ = H (x, y)` (since `H ≥ 0`).
  have h_eq :
      (fun y => ENNReal.ofReal (H (x, y))) =
        fun y => ENNReal.ofReal ‖H (x, y)‖ := by
    funext y
    have h_nonneg : 0 ≤ H (x, y) := hH_nonneg (x, y)
    have h_abs : |H (x, y)| = H (x, y) := abs_of_nonneg h_nonneg
    simp [Real.norm_eq_abs, h_abs]
  have hx_norm :
      ∫⁻ y, ENNReal.ofReal ‖H (x, y)‖ ∂μ < ∞ := by
    simpa [h_eq] using hx
  -- Use the standard Bochner criterion for integrability via the lintegral of the norm.
  -- Integrable is AEStronglyMeasurable ∧ HasFiniteIntegral
  have hx_hasFinite : HasFiniteIntegral (fun y => H (x, y)) μ := by
    -- HasFiniteIntegral means ∫⁻ y, ‖H (x, y)‖ₑ ∂μ < ⊤
    have h_enorm_eq : (fun y => ‖H (x, y)‖ₑ) = fun y => ENNReal.ofReal ‖H (x, y)‖ := by
      funext y
      exact (ofReal_norm_eq_enorm (H (x, y))).symm
    simpa [HasFiniteIntegral, h_enorm_eq] using hx_norm
  exact ⟨hx_aesm, hx_hasFinite⟩
end Newton
